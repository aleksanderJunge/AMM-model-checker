{-# LANGUAGE LambdaCase #-}
module Netting.Symbolic.SMT_opt where

import Netting.Sem
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe
import Data.List
import Data.Tuple.Extra
import Data.Ratio (denominator, numerator)
import System.Process ( readProcessWithExitCode )
import Control.Monad
import Control.Monad.Extra
import Netting.Symbolic.Concurrency

data Goal = U (String, [TokenAmt]) -- S State

-- A transaction guess, we attempt to guess a shape on the transaction and backtrack if we guess wrong
type TxGuess = (String, AtomicToken, AtomicToken)

checkGoal :: State -> Int -> [Goal] -> IO (Maybe (Int, IO String)) -- TODO: return transactions
checkGoal s k goals = do
    let tokens        = [T0, T1, T2] -- TODO: make this collect tokens from the configuration instead
        token_pairs   = S.fromList $ map (\(AMM (t, _) (t', _)) -> (t,t')) (fst s)
        names         = map name (snd s)
        combinations  = [(n, t0, t1) | n <- names, t0 <- tokens, t1 <- tokens, t0 /= t1, 
                                       (S.member (t0, t1) token_pairs) || (S.member (t1, t0) token_pairs) ]
        ks            = [1..k]
        guesses       = map (getGuesses combinations) ks
        guesses'      = map (filter check_adjacent_txns) guesses
        to_print      = zip3 ks guesses guesses'
    
    forM to_print (\(i, g, g') -> print $ "guesses to check at depth: " ++ (show i) ++ ": " ++ 
                                           (show $ length g') ++ " (reduced from: " ++ (show $ length g) ++ ")")


    satResult <- check goals conf ks guesses'
    case satResult of
        Nothing -> pure satResult
        res@(Just (depth, model)) -> do
            print $ "Solution found at depth: " ++ (show depth)
            model' <- model
            putStrLn model'
            pure res

    where 
        check goal conf [] guesses = pure Nothing
        check goal conf ks []      = pure Nothing 
        check goal conf (k:ks) (guess:guesses) = do
            res <- check_at_depth goal conf k guess
            case res of 
                Nothing  -> check goal conf ks guesses
                Just txs -> pure $ Just (k, liftM snd txs)
        check_at_depth goal conf k guesses = do
            txRes <- findM (\x -> liftM (not . fst) $ check_sat goal conf k x) guesses
            case txRes of 
                Nothing -> do 
                    print $ "No solution found at depth: " ++ (show k)
                    pure Nothing
                -- TODO: optimize to not run sat on this twice!
                Just txs -> pure . Just $ check_sat goal conf k txs
        check_sat goal conf k guess = do
            putStrLn $ show guess
            writeFile "/tmp/check_goal.smt2" (buildSMTQuery conf k True goal guess)
            (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
            case take 3 stdout of
                "sat"     -> pure (False, stdout)
                otherwise -> pure (True, stderr)
        getGuesses combs k = sequence $ replicate k combs
        check_adjacent_txns [] = True
        check_adjacent_txns (tx:[]) = True
        check_adjacent_txns (tx:txs) = (check_tx tx txs) && check_adjacent_txns txs
            where 
                check_tx tx []          = True
                check_tx tx@(n, t, t') ((n', t'', t'''):txs)
                    | n == n' && ((t == t'' && t' == t''') || (t == t''' && t' == t'' )) = False
                    | n /= n' && ((t == t'' && t' == t''') || (t == t''' && t' == t'' )) = True
                    | otherwise = check_tx tx txs



-- build query to check if goal is reachable within exactly k steps
buildSMTQuery :: State -> Int -> Bool -> [Goal] -> [TxGuess] -> String
buildSMTQuery s k getTxns goals guess =
    baseAxioms
    ++ buildVars k
    ++ constrainState s 0 -- (assuming s = g)
    ++ constrainTxns guess k
    ++ (unlines $ map buildChainAssertions [k])
    ++ (unlines $ map (\(U (n, amts)) -> userGoal amts k n) goals)
    ++ unlines ["(check-sat)"]
    ++ (unlines $ map (\i -> "(get-value (txn" ++ i ++ "))") $ map show [0..k-1])
    -- ++ "~" -- This is the EOF symbol for our worker threads to stop reading

-- a desired basket of tokens
userGoal :: [TokenAmt] -> Int -> String -> String
userGoal ts k n = unlines $
    map (\(t,v) -> 
        "(assert (>= (select (select (users state" ++ (show k) 
        ++ ") \"" ++ n ++ "\") " ++ (show t) ++ ") " ++ (showR v) ++ "))") ts

showR :: Rational -> String
showR r = "(/ " ++ (show $ numerator r) ++ " " ++ (show $ denominator r) ++ ")"

store :: String -> String -> String -> String
store a i e =
      "(store " ++ a ++ " " ++ i ++ " " ++ e ++ ")"

constrainState :: State -> Int -> String
constrainState (amms, users) i =
      let uassert = constrainUsers users i
          aassert = constrainAmms  amms  i
      in unlines $ [uassert, aassert]

showAMM :: AMM -> String
showAMM (AMM r0 r1) = 
    "(just (amm " ++ (showT r0) ++ " " ++ (showT r1) ++ "))"
    where 
      showT (t, v) = "(amount " ++ (show t) ++ " " ++ (showR v) ++ ")"

-- given list of AMMs initializes them in SMTLIB2 format.
constrainAmms :: [ AMM ] -> Int -> String
constrainAmms amms i =
    let topToks  = S.toList . S.fromList $ concatMap (\(AMM (t, _) (t', _)) -> [ t, t' ]) amms
        botDecls = map (bot_decl amms) topToks
        topDec   = top_decl botDecls topToks
    in
    unlines $ ["(assert (= (amms state" ++ (show i) ++ ") "] ++ [topDec] ++ ["))"]
    where 
        bot_decl amms topTok = 
            let amms'     = filter (\(AMM (t, _) (t', _)) ->  elem topTok [t, t']) amms
                botToks   = map    (\(AMM (t, _) (t', _)) -> (!! 0) $ filter (/= topTok) [t, t']) amms'
                storeAMM  = (\dec (amm, t) -> store dec (show t) (showAMM amm))
            in foldl storeAMM "lempt" (zip amms' botToks)
        top_decl botDecls topToks =
            let storeDecls = (\a (botDec, t) -> store a (show t) botDec)
            in foldl storeDecls "hempt" (zip botDecls topToks)


constrainUsers :: [ User ] -> Int -> String
constrainUsers users i = 
    -- TODO: once minted tokens are supported, remove toAtom check
    let users'   = map (\(User wal n) -> (n, catMaybes $ map toAtom $ M.toList wal)) users
        tsAndvs  = map unzip $ map snd users'
        userWals = map (\(ts, vs) -> fillWal ts vs) tsAndvs
        smtUsers = populateUsers (map fst users') userWals
    in
    unlines $ ["(assert (= (users state" ++ (show i) ++ ") "] ++ [smtUsers]++ ["))"]
    where 
        fillWal ts vs =
            let storeDecls = (\a (t, v) -> store a (show t) (showR v))
            in foldl storeDecls "baseWal" (zip ts vs)
        populateUsers ns wals =
            let storeDecls = (\a (n, wal) -> store a ("\"" ++ n ++ "\"") wal)
            in foldl storeDecls "baseUsers" (zip ns wals)
        toAtom =
            \case 
              (AtomTok a, v) -> Just (a, v)
              (MintTok _, _) -> Nothing

-- given a list of transaction guesses, constrains txns to match these
constrainTxns :: [ TxGuess ] -> Int -> String
constrainTxns guess k =
    let ks = [0..k-1]  -- TODO: add constraint that user's last transaciton must result in a positive balanc
        nameSet = map head . group . sort $ map fst3 guess
        lastOccurrence = M.fromList $ map (\(n,i) -> (n, (length guess) - i - 1 )) $ map (findFstOcc 0 (reverse guess)) nameSet 
        in
        unlines $ (makeGuess lastOccurrence guess ks) ++ (assertAmount ks)
    where 
        findFstOcc i [] n = (n, i-1) -- TODO: figure out some decent val here
        findFstOcc i (tx:txns) n = if n == (fst3 tx) then (n, i) else findFstOcc (i + 1) txns n
        makeGuess lastOcc guess ks = 
            map (\i -> unlines $
            [ "(assert (and"
            , if i == fromMaybe (-1) (M.lookup (fst3 $ guess !! i) lastOcc) 
                then "(forall ((tau Token)) (>= (getBal state" ++ (show $ i + 1) 
                     ++ " \"" ++ (fst3 $ guess !! i) ++ "\" tau) 0))"
              else ""
            , unlines $ ["  (= (user txn" ++ (show i) ++ ") \"" ++ ( fst3 $ guess!!i) ++ "\")"]
            , unlines $ ["  (= (t (from txn" ++ (show i) ++ ")) " ++ (show . snd3 $ guess!!i) ++ ")"]
            , unlines $ ["  (= (t (to   txn" ++ (show i) ++ ")) " ++ (show . thd3 $ guess!!i) ++ ")"]
            , "))"]) ks
        assertAmount ks = map (\i -> "(assert (> (v (from txn" ++ (show i) ++ ")) 0 ))") ks
            
-- Returns the necessary variables needed for executing i steps
buildVars :: Int -> String
buildVars i =
      unlines $ build_vars i []
      where 
          build_vars 0 s = unlines
            [ "( declare-const state" ++ (show 0) ++ " State)"] : s
          build_vars i s = build_vars (i - 1) (unlines 
            [ "( declare-const txn"   ++ (show $ i - 1) ++ " Txn)"
            , "( declare-const state" ++ (show i) ++ " State)"] : s)

buildChainAssertions :: Int -> String
buildChainAssertions i =
      unlines $ build_assertions i []
      where 
          build_assertions 0 s = s
          build_assertions i s = build_assertions (i - 1) 
            (unlines 
                [ "(assert (= state" ++ (show i) ++ " (swap state" ++ (show $ i - 1) ++ " txn" ++ (show $ i - 1) ++ ")))"] : s)


baseAxioms :: String
baseAxioms = unlines $
    [ "( declare-datatype Token ( ( t0 ) ( t1 ) ( t2 ) ))"
    , ""
    , "( declare-datatype TokenAmount ("
    , "    ( amount ( t Token ) (v Real) )"
    , "))"
    , ""
    , "( declare-datatype Amm ("
    , "    ( amm (r0 TokenAmount) (r1 TokenAmount) )"
    , "))"
    , ""
    , ""
    , "( declare-datatype Txn "
    , "    (( tx ( user String ) ( from TokenAmount ) ( to TokenAmount))"
    , "))"
    , ""
    , "(declare-datatypes ( (Pair 2) ) ("
    , "(par (X Y) ( (pair (fst X) (snd Y)) ))))"
    , ""
    , "( define-fun swaplr ((users (Array String (Array Token Real)))"
    , "                    (swp   Txn)"
    , "                    (inAmm Amm))"
    , "                    (Pair Amm (Array String (Array Token Real)))"
    , "("
    , "    let ((payout (/ (* (v (from swp)) (v (r1 inAmm)))"
    , "                    (+ (v (from swp)) (v (r0 inAmm))))))"
    , "         (ite (and (<= 0      (v (to swp)))"
    , "                   (<= (v (to swp)) payout))"
    , "              (let ((oldBal (select users (user swp))))"
    , "                ("
    , "                let ((newBal"
    , "                        (store"
    , "                            (store oldBal"
    , "                                   (t (to swp))"
    , "                                   (+ (select oldBal (t (to swp))) payout)"
    , "                            )"
    , "                            (t (from swp)) "
    , "                            (- (select oldBal (t (from swp)))"
    , "                               (v (from swp)))))"
    , "                     (newAmm (amm"
    , "                              (amount (t (from swp)) (+ (v (r0 inAmm)) (v (from swp))))"
    , "                              (amount (t (to swp)  ) (- (v (r1 inAmm)) payout))"
    , "                              ))"
    , "                     )"
    , "                (pair"
    , "                    newAmm"
    , "                    (store users (user swp) newBal)"
    , "                    )))"
    , "              (pair inAmm users)"
    , "        )"
    , "))"
    ,""
    , "( define-fun swaprl ((users (Array String (Array Token Real)))"
    , "                    (swp   Txn)"
    , "                    (inAmm Amm))"
    , "                    (Pair Amm (Array String (Array Token Real)))"
    , "("
    , "    let ((payout (/ (* (v (from swp)) (v (r0 inAmm)))"
    , "                    (+ (v (from swp)) (v (r1 inAmm))))))"
    , "         (ite (and (<= 0      (v (to swp)))"
    , "                   (<= (v (to swp)) payout))"
    , "              (let ((oldBal (select users (user swp))))"
    , "                ("
    , "                let ((newBal"
    , "                        (store"
    , "                            (store oldBal"
    , "                                   (t (to swp))"
    , "                                   (+ (select oldBal (t (to swp))) payout)"
    , "                            )"
    , "                            (t (from swp)) "
    , "                            (- (select oldBal (t (from swp)))"
    , "                               (v (from swp)))))"
    , "                     (newAmm (amm"
    , "                              (amount (t (to   swp)) (- (v (r0 inAmm)) payout))"
    , "                              (amount (t (from swp)) (+ (v (r1 inAmm)) (v (from swp))))"
    , "                              ))"
    , "                     )"
    , "                (pair"
    , "                    newAmm"
    , "                    (store users (user swp) newBal)"
    , "                    )))"
    , "              (pair inAmm users)"
    , "        )"
    , "))"
    , ""
    , "( define-fun getBal ((users (Array String (Array Token Real)))"
    , "                     (name String)"
    , "                     (tau  Token)) "
    , "                      Real "
    , "("
    , "    select (select users name) tau"
    , "))"
    , ""
    , "(define-fun baseUsers () (Array String (Array Token Real))"
    , "((as const (Array String (Array Token Real)))"
    , "         ((as const (Array Token Real)) 0.0)))"
    , ""
    , "(define-fun baseWal () (Array Token Real)"
    , "((as const (Array Token Real)) 0.0))"
    ]