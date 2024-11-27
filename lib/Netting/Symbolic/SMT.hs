{-# LANGUAGE LambdaCase #-}
module Netting.Symbolic.SMT where

import Netting.Symbolic.Interpreter.Parser
import Netting.Symbolic.Interpreter.SymTab
import Netting.Symbolic.Sem
import Data.Maybe
import Data.List
import Data.Either
import qualified Data.Map as M
import qualified GHC.Utils.Misc as Util
import qualified Text.Read as TR
import System.IO

-- We currently only support "EF (Property)"
data Query = EF Expr
  deriving (Show) --TODO: remove this

type Symtable = Env String SType

type TxGuess = (String, String, String)

buildSMTQuery :: ([SAMM], [SUser], [Assert]) -> [SMTStmt Decl Assert] -> Symtable -> Int -> (String, [String]) -> [TxGuess] -> Query -> Either String String
buildSMTQuery ([], _, _) _ _ _ _ _ _ = Left "No AMMS"
buildSMTQuery (_, [], _) _ _ _ _ _ _ = Left "No Users"
buildSMTQuery (samms, susers, assertions) stmts stab k (tokdec, toks) guess query =
    Right $
    unlines [ tokdec ] 
    ++ baseAxioms
    ++ showStmts stmts
    ++ unlines [ show $ decorateWithDepth query stab k ]
    -- ++ buildVars k
    -- ++ constrainState s 0 -- (assuming s = g)
    -- ++ constrainTxns guess k
    -- ++ (unlines $ map buildChainAssertions [k])
    -- ++ (unlines $ map (\(U (n, amts)) -> userGoal amts k n) goals)
    ++ unlines ["(check-sat)"]
    ++ (unlines $ map (\i -> "(get-value (txn" ++ i ++ "))") $ map show [0..k-1])
  
-- this could be somewhat limiting in the sense that there's no way to compare variables across different time steps in the query language
decorateWithDepth :: Query -> Symtable -> Int -> Assert
decorateWithDepth (EF exp) stab k =
  Assert $ decorate exp stab k 
  where 
    decorate :: Expr -> Symtable -> Int -> Expr
    decorate (Var n) stab k   =
      case get stab n of
        Just DAmm  -> (Var $ n ++ (show k))
        Just DUser -> (select (Var $ "users" ++ (show k)) (Var $ "\""++ n ++ "\""))
        _          -> (Var n)
    decorate (LReal r) stab k = (LReal r)
    decorate (LBool b) stab k = (LBool b)
    decorate (UnOp unop e) stab k          = UnOp unop (decorate e stab k)
    decorate (BinOp binop e1 e2) stab k    = BinOp binop (decorate e1 stab k) (decorate e2 stab k)
    decorate (TerOp terop e1 e2 e3) stab k = TerOp terop (decorate e1 stab k) (decorate e2 stab k) (decorate e3 stab k)
    decorate exp _ _ = exp
 
-- TODO: enable parsing more numbers and check for subzero
makeAmm :: SAMM -> Symtable -> Either String ([SMTStmt Decl Assert], Env String SType)
makeAmm (SAMM n (v, t) (v', t')) stab =
    if isJust (get stab n) then Left $ n ++ " already declared!"
    else if not (checkTok stab t)  then Left $ "Token: " ++ (fromMaybe "?" t ) ++ " doesn't exist" ++ " in stab: " ++ (show stab)
    else if not (checkTok stab t') then Left $ "Token: " ++ (fromMaybe "?" t') ++ " doesn't exist" ++ " in stab: " ++ (show stab)
    else 
    let amm_name = singleton . Dec $ DeclVar n TAmm
        val_v    = fromMaybe [] ( v  >>= (\v -> Just [Ass . Assert $ eq (LReal v)  (getv . getr0 $ Var n)] ))
        val_v'   = fromMaybe [] ( v' >>= (\v -> Just [Ass . Assert $ eq (LReal v)  (getv . getr1 $ Var n)] ))
        val_t    = fromMaybe [] ( t  >>= (\t -> Just [Ass . Assert $ eq (LTok  t)  (gett . getr0 $ Var n)] ))
        val_t'   = fromMaybe [] ( t' >>= (\t -> Just [Ass . Assert $ eq (LTok  t)  (gett . getr1 $ Var n)] ))
        distinctness = [Ass . Assert $ distinct (gett . getr0 $ Var n) (gett . getr1 $ Var n)]
        pos_v   = if null val_v  then [Ass . Assert $ lt (LReal 0) (getv . getr0 $ Var n)] else []
        pos_v'  = if null val_v' then [Ass . Assert $ lt (LReal 0) (getv . getr1 $ Var n)] else []
        stab' = bind stab (n, DAmm)
    in Right (amm_name ++ val_v ++ val_v' ++ val_t ++ val_t' ++ distinctness ++ pos_v ++ pos_v', stab')
    where 
        checkTok stab (Just tok_name) =
            let tt = get stab tok_name in
            if isJust tt && (fromJust tt == DTok) then True else False
        checkTok stab Nothing = True -- If token isn't declared, it's fine

--constrainTxns :: [ TxGuess ] -> Int -> String
--constrainTxns guess k =
--    let ks = [0..k-1]  -- TODO: add constraint that user's last transaciton must result in a positive balanc
--        nameSet = map head . group . sort $ map fst3 guess
--        lastOccurrence = M.fromList $ map (\(n,i) -> (n, (length guess) - i - 1 )) $ map (findFstOcc 0 (reverse guess)) nameSet 
--        in
--        unlines $ (makeGuess lastOccurrence guess ks) ++ (assertAmount ks)
--    where 
--        findFstOcc i [] n = (n, i-1) -- TODO: figure out some decent val here
--        findFstOcc i (tx:txns) n = if n == (fst3 tx) then (n, i) else findFstOcc (i + 1) txns n
--        makeGuess lastOcc guess ks = 
--            map (\i -> unlines $
--            [ "(assert (and"
--            , if i == fromMaybe (-1) (M.lookup (fst3 $ guess !! i) lastOcc) 
--                then "(forall ((tau Token)) (>= (getBal state" ++ (show $ i + 1) 
--                     ++ " \"" ++ (fst3 $ guess !! i) ++ "\" tau) 0))"
--              else ""
--            , unlines $ ["  (= (user txn" ++ (show i) ++ ") \"" ++ ( fst3 $ guess!!i) ++ "\")"]
--            , unlines $ ["  (= (t (from txn" ++ (show i) ++ ")) " ++ (show . snd3 $ guess!!i) ++ ")"]
--            , unlines $ ["  (= (t (to   txn" ++ (show i) ++ ")) " ++ (show . thd3 $ guess!!i) ++ ")"]
--            , "))"]) ks
--        assertAmount ks = map (\i -> "(assert (> (v (from txn" ++ (show i) ++ ")) 0 ))") ks

collectUsers :: Env String SType -> Int -> Either String ([SMTStmt Decl Assert], Env String SType)
collectUsers stab i = 
    let cname      = "users" ++ (show i) in
    if isJust (get stab cname ) then Left $ " user collection already defined for depth: " ++ (show i) else
    let users      = map fst (filter (\(k,v) -> v == DUser) (M.toList stab))
        usersState = [Ass . Assert $  eq (Var cname) (foldl (\acc u -> store acc (Var ("\"" ++ u ++ "\"")) (Var u)) (Var "baseUsers") users)]
        --assertions = concat $ map (\u -> [Ass . Assert $ eq (Var u) (select (Var cname) ()) ]) users
        stab'      = bind stab (cname, DUsers)
    in Right (usersState, stab')

-- TODO: opt point, maybe completely concretize wallet by storing rather than selecting tokens from it 
makeUser :: SUser -> Symtable -> Either String ([SMTStmt Decl Assert], Env String SType)
makeUser (SUser wal n) stab =
    if isJust (get stab n) then Left $ n ++ " already declared!"
    else if any (\t -> not $ checkTok stab t) (map fst wal)  then Left $ " one or more tokens not found in: " ++ show stab
    else if length (map fst wal) /= length (nub $ map fst wal) then Left " some tokens are declared twice"
    else 
    let user_name = singleton . Dec $ DeclVar n (TArray TToken TReal) -- nest this inside a TArray TUser
        wal_dom   = nub $ map fst wal
        stab_dom  = nub $ map fst (filter (\(k,v) -> v == DTok) (M.toList stab))
        undef     = stab_dom \\ wal_dom -- these will be set to 0
        conc_wal  = Util.mapSnd fromJust (filter (\(k,v) -> isJust v) wal)
        symb_wal  = filter (\(k,v) -> isNothing v) wal
        conc_ass  = concat $ map (\(t,v) -> [Ass . Assert $ eq (select (Var n) (LTok t)) (LReal v)]) conc_wal
        symb_ass  = concat $ map (\(t,_) -> [Dec $ DeclVar (n ++ "_" ++ t) TReal, Ass . Assert $ eq (select (Var n) (LTok t)) (Var $ n ++ "_" ++ t)]) symb_wal
        undef_ass = concat $ map (\t     -> [Ass . Assert $ eq (select (Var n) (LTok t)) (LReal 0)]) undef
        stab' = bind stab (n, DUser)
    in Right (user_name ++ conc_ass ++ symb_ass ++ undef_ass, stab')
    where 
        checkTok stab tok_name =
            let tt = get stab tok_name in
            if isJust tt && (fromJust tt == DTok) then True else False

-- given a list of names, declares these to be the set of tokens
declToks :: SToks -> Symtable -> Either String (String, Env String SType, [String]) -- third element is the list of tokens declared (to be used in haskell for further processing)
declToks (SToks toks) stab =
    if elem DTok (codomain stab) then Left "Tokens have already been declared!" else
        let stab' = foldl (\st tok -> bind st (tok, DTok)) stab toks
            decl  = "(declare-datatype Token ("++ (concat $ intersperse " " $ map (\x -> '(':x ++ ")") toks) ++ "))"
        in Right (decl, stab', toks)
        
showStmts :: [SMTStmt Decl Assert] -> String
showStmts stmts = 
    let (decs, asses) = partition (\case {Dec _ -> True; Ass _ -> False}) stmts in
    unlines $ map showStmt (decs ++ asses)
    where 
        showStmt =
            \case
                Dec decl -> show decl
                Ass ass  -> show ass


-- TODO: returns Left (Reason for failure) or Right (success)
--checkAMMConsistency :: [SMTStmt Decl Assert] -> [String] -> Either String Bool
--checkAMMConsistency stmts toks = undefined
   -- let ammdecls = filter (\stmt -> \case {
   --     Dec (DeclVar _ dt) 
   --         | dt == TAmm -> True;
   --     _                -> False
   -- }) stmts 
   -- let 

-- Returns the necessary variables needed for executing i steps
--buildVars :: Int -> String
--buildVars i =
--      unlines $ build_vars i []
--      where 
--          build_vars 0 s = unlines
--            [ "( declare-const state" ++ (show 0) ++ " State)"] : s
--          build_vars i s = build_vars (i - 1) (unlines 
--            [ "( declare-const txn"   ++ (show $ i - 1) ++ " Txn)"
--            , "( declare-const users" ++ (show i) ++ " State)"] : s)

baseAxioms :: String
baseAxioms = unlines $
    [ "( declare-datatype TokenAmount ("
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
    , "(define-fun baseUsers () (Array String (Array Token Real))"
    , "((as const (Array String (Array Token Real)))"
    , "         ((as const (Array Token Real)) 0.0)))"
    , ""
    -- , "(define-fun baseWal () (Array Token Real)" --TODO: remove if not needed
    -- , "((as const (Array Token Real)) 0.0))"
    ]

--
---- A transaction guess, we attempt to guess a shape on the transaction and backtrack if we guess wrong
--type TxGuess = (String, AtomicToken, AtomicToken)
--
--checkGoal :: Configuration -> Int -> [Goal] -> IO (Maybe (Int, IO String)) -- TODO: return transactions
--checkGoal conf@(Configuration g s q) k goals = do
--    let tokens        = [T0, T1, T2] -- TODO: make this collect tokens from the configuration instead
--        token_pairs   = S.fromList $ map (\(AMM (t, _) (t', _)) -> (t,t')) (fst g)
--        names         = map name (snd g)
--        combinations  = [(n, t0, t1) | n <- names, t0 <- tokens, t1 <- tokens, t0 /= t1, 
--                                       (S.member (t0, t1) token_pairs) || (S.member (t1, t0) token_pairs) ]
--        ks            = [1..k]
--        guesses       = map (getGuesses combinations) ks
--        guesses'      = map (filter check_adjacent_txns) guesses
--        to_print      = zip3 ks guesses guesses'
--    
--    forM to_print (\(i, g, g') -> print $ "guesses to check at depth: " ++ (show i) ++ ": " ++ 
--                                           (show $ length g') ++ " (reduced from: " ++ (show $ length g) ++ ")")
--
--
--    --satResult <- check' goals conf ks guesses'
--    --case satResult of
--    --    Nothing -> pure satResult
--    --    res@(Just (depth, model)) -> do
--    --        print $ "Solution found at depth: " ++ (show depth)
--    --        putStrLn model
--    --        pure res
--    satResult <- check goals conf ks guesses'
--    case satResult of
--        Nothing -> pure satResult
--        res@(Just (depth, model)) -> do
--            print $ "Solution found at depth: " ++ (show depth)
--            model' <- model
--            putStrLn model'
--            pure res
--
--    where 
--        check goal conf [] guesses = pure Nothing
--        check goal conf ks []      = pure Nothing 
--        check goal conf (k:ks) (guess:guesses) = do
--            res <- check_at_depth goal conf k guess
--            case res of 
--                Nothing  -> check goal conf ks guesses
--                Just txs -> pure $ Just (k, liftM snd txs)
--        check' goal conf [] guesses = pure Nothing
--        check' goal conf ks []      = pure Nothing 
--        check' goal conf (k:ks) (guess:guesses) = do
--            res <- check_at_depth' goal conf k guess
--            case res of
--                Nothing -> do 
--                    print $ "No solution found at depth: " ++ (show k)
--                    check' goal conf ks guesses
--                Just out -> pure $ Just (k, out)
--        check_at_depth' goal conf k guesses = do 
--            let queries = map (buildSMTQuery conf k False goal) guesses 
--                threads = zip [0..9] (take 10 queries)-- TODO: take an input number of threads to spawn & check whether 6 <= |queries|
--            initJobs <- mapM (\(tid, query) -> createJob tid query) threads
--            managePool initJobs queries
--        --check_at_depth'' goal conf k guesses = do
--        --    let queries          = map (buildSMTQuery conf k False goal) guesses 
--        --        num_threads      = 6
--        --        (init, queries') = splitAt num_threads queries
--        --    workers <- createWorkers num_threads
--        --    initWorkers workers init
--        --    runOnPool workers queries'
--        check_at_depth goal conf k guesses = do
--            txRes <- findM (\x -> liftM (not . fst) $ check_sat goal conf k x) guesses
--            case txRes of 
--                Nothing -> do 
--                    print $ "No solution found at depth: " ++ (show k)
--                    pure Nothing
--                -- TODO: optimize to not run sat on this twice!
--                Just txs -> pure . Just $ check_sat goal conf k txs
--        check_sat goal conf k guess = do
--            putStrLn $ show guess
--            writeFile "/tmp/check_goal.smt2" (buildSMTQuery conf k True goal guess)
--            (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
--            case take 3 stdout of
--                "sat"     -> pure (False, stdout)
--                otherwise -> pure (True, stderr)
--        getGuesses combs k = sequence $ replicate k combs
--        check_adjacent_txns [] = True
--        check_adjacent_txns (tx:[]) = True
--        check_adjacent_txns (tx:txs) = (check_tx tx txs) && check_adjacent_txns txs
--            where 
--                check_tx tx []          = True
--                check_tx tx@(n, t, t') ((n', t'', t'''):txs)
--                    | n == n' && ((t == t'' && t' == t''') || (t == t''' && t' == t'' )) = False
--                    | n /= n' && ((t == t'' && t' == t''') || (t == t''' && t' == t'' )) = True
--                    | otherwise = check_tx tx txs
--
--
--
---- build query to check if goal is reachable within exactly k steps
--buildSMTQuery :: Configuration -> Int -> Bool -> [Goal] -> [TxGuess] -> String
--buildSMTQuery (Configuration g s q) k getTxns goals guess =
--    baseAxioms
--    ++ buildVars k
--    ++ constrainState s 0 -- (assuming s = g)
--    ++ constrainTxns guess k
--    ++ (unlines $ map buildChainAssertions [k])
--    ++ (unlines $ map (\(U (n, amts)) -> userGoal amts k n) goals)
--    ++ unlines ["(check-sat)"]
--    ++ (unlines $ map (\i -> "(get-value (txn" ++ i ++ "))") $ map show [0..k-1])
--    -- ++ "~" -- This is the EOF symbol for our worker threads to stop reading
--
---- a desired basket of tokens
--userGoal :: [TokenAmt] -> Int -> String -> String
--userGoal ts k n = unlines $
--    map (\(t,v) -> 
--        "(assert (>= (select (select (users state" ++ (show k) 
--        ++ ") \"" ++ n ++ "\") " ++ (show t) ++ ") " ++ (showR v) ++ "))") ts
--
--showR :: Rational -> String
--showR r = "(/ " ++ (show $ numerator r) ++ " " ++ (show $ denominator r) ++ ")"
--
--store :: String -> String -> String -> String
--store a i e =
--      "(store " ++ a ++ " " ++ i ++ " " ++ e ++ ")"
--
--constrainState :: State -> Int -> String
--constrainState (amms, users) i =
--      let uassert = constrainUsers users i
--          aassert = constrainAmms  amms  i
--      in unlines $ [uassert, aassert]
--
--showAMM :: AMM -> String
--showAMM (AMM r0 r1) = 
--    "(just (amm " ++ (showT r0) ++ " " ++ (showT r1) ++ "))"
--    where 
--      showT (t, v) = "(amount " ++ (show t) ++ " " ++ (showR v) ++ ")"
--
---- given list of AMMs initializes them in SMTLIB2 format.
--constrainAmms :: [ AMM ] -> Int -> String
--constrainAmms amms i =
--    let topToks  = S.toList . S.fromList $ concatMap (\(AMM (t, _) (t', _)) -> [ t, t' ]) amms
--        botDecls = map (bot_decl amms) topToks
--        topDec   = top_decl botDecls topToks
--    in
--    unlines $ ["(assert (= (amms state" ++ (show i) ++ ") "] ++ [topDec] ++ ["))"]
--    where 
--        bot_decl amms topTok = 
--            let amms'     = filter (\(AMM (t, _) (t', _)) ->  elem topTok [t, t']) amms
--                botToks   = map    (\(AMM (t, _) (t', _)) -> (!! 0) $ filter (/= topTok) [t, t']) amms'
--                storeAMM  = (\dec (amm, t) -> store dec (show t) (showAMM amm))
--            in foldl storeAMM "lempt" (zip amms' botToks)
--        top_decl botDecls topToks =
--            let storeDecls = (\a (botDec, t) -> store a (show t) botDec)
--            in foldl storeDecls "hempt" (zip botDecls topToks)
--
--
--constrainUsers :: [ User ] -> Int -> String
--constrainUsers users i = 
--    -- TODO: once minted tokens are supported, remove toAtom check
--    let users'   = map (\(User wal n) -> (n, catMaybes $ map toAtom $ M.toList wal)) users
--        tsAndvs  = map unzip $ map snd users'
--        userWals = map (\(ts, vs) -> fillWal ts vs) tsAndvs
--        smtUsers = populateUsers (map fst users') userWals
--    in
--    unlines $ ["(assert (= (users state" ++ (show i) ++ ") "] ++ [smtUsers]++ ["))"]
--    where 
--        fillWal ts vs =
--            let storeDecls = (\a (t, v) -> store a (show t) (showR v))
--            in foldl storeDecls "baseWal" (zip ts vs)
--        populateUsers ns wals =
--            let storeDecls = (\a (n, wal) -> store a ("\"" ++ n ++ "\"") wal)
--            in foldl storeDecls "baseUsers" (zip ns wals)
--        toAtom =
--            \case 
--              (AtomTok a, v) -> Just (a, v)
--              (MintTok _, _) -> Nothing
--
---- given a list of transaction guesses, constrains txns to match these
--constrainTxns :: [ TxGuess ] -> Int -> String
--constrainTxns guess k =
--    let ks = [0..k-1]  -- TODO: add constraint that user's last transaciton must result in a positive balanc
--        nameSet = map head . group . sort $ map fst3 guess
--        lastOccurrence = M.fromList $ map (\(n,i) -> (n, (length guess) - i - 1 )) $ map (findFstOcc 0 (reverse guess)) nameSet 
--        in
--        unlines $ (makeGuess lastOccurrence guess ks) ++ (assertAmount ks)
--    where 
--        findFstOcc i [] n = (n, i-1) -- TODO: figure out some decent val here
--        findFstOcc i (tx:txns) n = if n == (fst3 tx) then (n, i) else findFstOcc (i + 1) txns n
--        makeGuess lastOcc guess ks = 
--            map (\i -> unlines $
--            [ "(assert (and"
--            , if i == fromMaybe (-1) (M.lookup (fst3 $ guess !! i) lastOcc) 
--                then "(forall ((tau Token)) (>= (getBal state" ++ (show $ i + 1) 
--                     ++ " \"" ++ (fst3 $ guess !! i) ++ "\" tau) 0))"
--              else ""
--            , unlines $ ["  (= (user txn" ++ (show i) ++ ") \"" ++ ( fst3 $ guess!!i) ++ "\")"]
--            , unlines $ ["  (= (t (from txn" ++ (show i) ++ ")) " ++ (show . snd3 $ guess!!i) ++ ")"]
--            , unlines $ ["  (= (t (to   txn" ++ (show i) ++ ")) " ++ (show . thd3 $ guess!!i) ++ ")"]
--            , "))"]) ks
--        assertAmount ks = map (\i -> "(assert (> (v (from txn" ++ (show i) ++ ")) 0 ))") ks
--            
---- Returns the necessary variables needed for executing i steps
--buildVars :: Int -> String
--buildVars i =
--      unlines $ build_vars i []
--      where 
--          build_vars 0 s = unlines
--            [ "( declare-const state" ++ (show 0) ++ " State)"] : s
--          build_vars i s = build_vars (i - 1) (unlines 
--            [ "( declare-const txn"   ++ (show $ i - 1) ++ " Txn)"
--            , "( declare-const state" ++ (show i) ++ " State)"] : s)
--
--buildChainAssertions :: Int -> String
--buildChainAssertions i =
--      unlines $ build_assertions i []
--      where 
--          build_assertions 0 s = s
--          build_assertions i s = build_assertions (i - 1) 
--            (unlines 
--                [ "(assert (= state" ++ (show i) ++ " (swap state" ++ (show $ i - 1) ++ " txn" ++ (show $ i - 1) ++ ")))"] : s)
--
--
--baseAxioms :: String
--baseAxioms = unlines $
--  [ "( declare-datatype Token ( ( t0 ) ( t1 ) ( t2 ) ))"
--  , ""
--  , "( declare-datatype TokenAmount ("
--  , "    ( amount ( t Token ) (v Real) )"
--  , "))"
--  , ""
--  , "( declare-datatype Amm ("
--  , "    ( amm (r0 TokenAmount) (r1 TokenAmount) )"
--  , "))"
--  , ""
--  , "( declare-datatypes (( Maybe 1 )) ("
--  , "( par ( X ) ( ( nothing ) ( just ( val X ))))))"
--  , ""
--  , "( declare-datatype State ("
--  , "    (pair (amms  (Array Token (Array Token (Maybe Amm))))"
--  , "          (users (Array String (Array Token Real)))"
--  , "    )"
--  , "))"
--  , ""
--  , "( declare-datatype Txn (( tx ( user String ) ( from TokenAmount ) ( to TokenAmount))))"
--  , ""
--  , "( define-fun swap ((state State)"
--  , "                   (swp   Txn))"
--  , "                   State"
--  , "("
--  , "     ite (> 0 (v (from swp))) state"
--  , "    (let ((foundAmm (select (select (amms state) (t (from swp))) (t (to swp)))))"
--  , "        ( match foundAmm ((nothing state) ((just foundAmmX)"
--  , "        (let ((swappingAmm ("
--  , "            ite (= (t (r0 foundAmmX)) (t (from swp)))"
--  , "                   foundAmmX"
--  , "                   (amm (r1 foundAmmX) (r0 foundAmmX)))))"
--  --, "        ; Calculate payout"
--  , "        (let ((payout (/ (* (v (from swp)) (v (r1 swappingAmm)))"
--  , "                         (+ (v (from swp)) (v (r0 swappingAmm))))))"
--  --, "              ; If swap withing x-rate, then execute, otherwise leave state unchanged"
--  , "             (ite (and (<= 0      (v (to swp)))"
--  , "                       (<= (v (to swp)) payout))"
--  , "                  (let ((oldBal (select (users state) (user swp))))"
--  , "                    ("
--  , "                    let ((newBal"
--  , "                            (store"
--  , "                                (store oldBal"
--  , "                                       (t (to swp))"
--  , "                                       (+ (select oldBal (t (to swp))) payout)"
--  , "                                )"
--  , "                                (t (from swp)) "
--  , "                                (- (select oldBal (t (from swp)))"
--  , "                                   (v (from swp)))))"
--  , "                         (newAmm (amm"
--  , "                                  (amount (t (from swp)) (+ (v (r0 swappingAmm)) (v (from swp))))"
--  , "                                  (amount (t (to swp)  ) (- (v (r1 swappingAmm)) payout))"
--  , "                                  ))"
--  , "                         )"
--  --, "                    ; return new state"
--  , "                    (pair"
--  , "                        (let ((oldTFromAmms (select (amms state) (t (from swp))))"
--  , "                              (oldTToAmms   (select (amms state) (t (to swp)  ))))"
--  --, "                              ; update lookup corresponding to selecting t0 -> t1"
--  , "                             (let ((tmpamms (store (amms state ) (t (from swp))"
--  , "                                (store oldTFromAmms (t (to swp)) (just newAmm)))))"
--  , "                              (store tmpamms (t (to swp)) (store oldTToAmms (t (from swp)) (just newAmm)))))"
--  , "                        (store (users state) (user swp) newBal)"
--  , "                        )))"
--  , "                  state"
--  , "            )"
--  , "    )"
--  , ")))))))"
--  , "( define-fun getBal ((state State)"
--  , "                     (name String)"
--  , "                     (tau  Token)) "
--  , "                      Real "
--  , "("
--  , "    select (select (users state) name) tau"
--  , "))"
--  , "(define-fun lempt () (Array Token (Maybe Amm))"
--  , "((as const (Array Token (Maybe Amm))) nothing))"
--  , "(define-fun hempt () (Array Token (Array Token (Maybe Amm)))"
--  , "((as const (Array Token (Array Token (Maybe Amm)))) lempt))" 
--  , "(define-fun baseUsers () (Array String (Array Token Real))"
--  , "((as const (Array String (Array Token Real)))"
--  , "         ((as const (Array Token Real)) 0.0)))"
--  , "(define-fun baseWal () (Array Token Real)"
--  , "((as const (Array Token Real)) 0.0))"
--  ]