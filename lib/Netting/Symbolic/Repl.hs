{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Repl where

import Netting.Symbolic.Interpreter.Parser
import Netting.Symbolic.Interpreter.SymTab
import Netting.Symbolic.Sem
import Netting.Symbolic.SMT
import Netting.Symbolic.Utils
import Data.Maybe
import Data.Char
import Data.List
import Data.Either
import Data.Either.Extra
import qualified Data.Map as M
import qualified GHC.Utils.Misc as Util
import qualified Text.Read as TR
import System.IO
import System.Process ( readProcessWithExitCode )
import Control.Monad
import Control.Monad.Extra
import Debug.Trace

repl :: IO ()
repl = do
  let symtab = empty :: Env String SType
  --putStrLn "Declare tokens"
  (stab', toknames) <- toks_ symtab 
  --putStrLn "Define initial state"
  depth <- getDepth
  (stab'', stmts, amms, users) <- init_ stab' [] [] []
  let useFee      = any (\(SAMM _ _ _ fee) -> case fee of None -> False; _ -> True) amms
      defaultFees = if useFee then setDefaultFees amms [] else []
 -- case collectUsers stab'' 0 of
 --   Left e -> putStrLn "you probably defined a variable called users0, it's reserved... start over"
 --   Right (users0, stab''') -> do
  --putStrLn "initial state looks like:"
  --putStrLn $ showStmts (stmts ++ users0)
  --putStrLn "Set constraints"
  (constraints) <- constrain stab'' []
  ----putStrLn "How deep to check?"
  let combs  =  getCombinations useFee (amms, users) depth
  satResult <- check (buildSMTQuery (amms,users,(stmts ++ defaultFees)) useFee stab'' toknames constraints) [0..depth] combs
  case satResult of
      Nothing -> do {putStrLn "no solution found"; return ()}
      res@(Just (depth, model, txs)) -> do
          putStrLn $ "Solution found at depth " ++ (show depth)
          model' <- model
          let ftpr0r1  = read_model stab'' txs model'
              model''  = zip ftpr0r1 txs
              to_print = map print_txn model''
              amms     = pair_amms_tx stab'' txs

          mapM putStrLn to_print
          return ()
                --repl 
  where
    toks_ stab = do
      --putStr ">> "
      --hFlush stdout
      line <- getLine
      case TR.readMaybe line :: Maybe SToks of 
        Just toks -> do
            case declToks toks stab of
                Left e -> do {putStrLn e; toks_ stab}
                Right (stab', toklst) -> do 
                    --putStrLn r
                    if length (nub toklst) /= length toklst then do {putStrLn "duplicate token..."; toks_ stab}
                    else return (stab', toklst)
        Nothing -> do {putStrLn "declare tokens, e.g.: TOKENS: (t0, t1, t2)"; toks_ stab}

    getDepth = do
      --putStr ">> "
      --hFlush stdout
      line <- getLine
      if take 5 line == "DEPTH" then 
        case TR.readMaybe (drop 5 line) :: Maybe Int of 
          Just i -> pure i
          Nothing -> do {putStrLn "Please enter an Int as depth:"; getDepth}
      else getDepth

    init_ stab stmts amms users = do
      --putStr ">> "
      --hFlush stdout
      line <- getLine
      if take 5 line == "BEGIN" then return (stab, stmts, amms, users)
      else case TR.readMaybe line :: Maybe SAMM of
        Just samm -> do
          case makeAmm samm stab of
            Left e -> do {putStrLn e; init_ stab stmts amms users}
            Right (r, stab') -> do 
                --putStrLn $ showStmts r
                --putStrLn $ show stab'
                init_ stab' (stmts ++ r) (samm : amms) users
        Nothing ->
            case TR.readMaybe line :: Maybe SUser of 
            Just user ->
                case makeUser user stab of
                Left e -> do {putStrLn e; init_ stab stmts amms users}
                Right (r, stab') -> do 
                    --putStrLn $ showStmts r 
                    init_ stab' (stmts ++ r) amms (user : users)
            Nothing -> do
                --putStrLn $ "Didn't catch that"
                init_ stab stmts amms users

    constrain stab acc = do
      --putStr ">> "
      --hFlush stdout
      line <- getLine
      case line of
        'I':'N':'I':'T':s -> 
          case parse stab s of
            Right exp -> do 
                --putStrLn "adding constraint:"
                --putStrLn $ show (INIT exp)
                constrain stab (acc ++ [INIT exp])
            Left e    -> do {putStrLn e; constrain stab acc}
        'E':'F':s   ->
          case parse stab s of
            Right exp -> do 
                --putStrLn "adding constraint:"
                --putStrLn $ show (EF exp)
                constrain stab (acc ++ [EF exp])
            Left e    -> do {putStrLn e; constrain stab acc}
        'E':'U':s   ->
          let (blank1, rest1) = readUntil '(' s
              (exp1,   rest2) = readUntil ')' rest1
              (blank2, rest3) = readUntil '(' rest2
              (exp2, _)       = readUntil ')' rest3
          in if any ((==) "!") [blank1, exp1, blank2, exp2] then
            do {putStrLn "failed reading EU, syntax is: EU (exp1) (exp2)"; constrain stab acc} else
            case parse stab exp1 of
              Right exp1 ->
                case parse stab exp2 of
                  Right exp2 -> do 
                    constrain stab (acc ++ [EU exp1 exp2])
                  Left e -> do {putStrLn e; constrain stab acc}
              Left e    -> do {putStrLn e; constrain stab acc}
        'E':'N':'D':s -> return acc
        _        -> constrain stab acc

    check buildQuery [] guesses = pure Nothing
    check buildQuery ks []      = pure Nothing 
    check buildQuery (k:ks) (guess:guesses) = do
        res <- check_at_depth buildQuery k guess
        case res of 
            Nothing  -> check buildQuery ks guesses
            Just (out, txs) -> do 
              pure $ Just (k, liftM snd out, txs)
    check_at_depth buildQuery k guesses = do
        txRes <- findM (\x -> liftM (not . fst) $ check_sat buildQuery k x) guesses
        case txRes of 
            Nothing -> do 
                putStrLn $ "No solution found at depth: " ++ (show k)
                pure Nothing
            -- TODO: optimize to not run sat on this twice!
            Just txs -> pure . Just $ (check_sat buildQuery k txs, txs)
    check_sat buildQuery k guess = do
        --putStrLn $ show guess
        writeFile "/tmp/check_goal.smt2" (case buildQuery guess k of {Left e -> error e; Right r -> r})
        (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
        case take 3 stdout of
            "sat"     -> pure (False, stdout)
            otherwise -> pure (True, stderr)
    pair_amms_tx stab txns = 
      let amms  = filter (\(k,v) -> case v of DAmm _ _ -> True; _ -> False) (M.toList stab)
          pairs = map (\(_, t0, t1) -> find (\case {(k, DAmm t0' t1') -> (t0' == t0 && t1' == t1) || 
                                                                         (t0' == t1 && t1' == t0); _ -> False}) amms) txns
          unjust = catMaybes pairs
      in if length pairs /= length unjust then Left "one amm pair not found" else 
      let unwrapped = catMaybes $ map (\case {(n, DAmm t0 t1) -> return (n, t0, t1); _ -> Nothing}) unjust
          withdir = zipWith3 (\(n, t0, t1) (_, t0', t1') i -> 
            if t0 == t0' then ("l" +@ n +@ i, "r" +@ n +@ i) else ("r" +@ n +@ i, "l" +@ n +@ i)) 
              unwrapped txns (map show [1..(length txns)])
      in return withdir
    
    read_model stab txs model =
      let --terms   = toTerms model
          --tabled  = map (span (\c -> isAlphaNum c || c == '_')) terms
          pairs  = toTerms model
          pairs' = filter (\(f, s) -> not $ null f || null s) pairs
          from    = map snd . sort $ (filter (\(f, s)-> (take 4 f) == "from") pairs') -- TODO: sort these !!!!! and below
          to      = map snd . sort $ (filter (\(f, s)-> (take 2 f) == "to") pairs')
          payout  = map snd . sort $ (filter (\(f, s)-> (take 6 f) == "payout") pairs')
          (r0s, r1s) = unzip $ fromRight' $ pair_amms_tx stab txs -- TODO: make better error handling here, also below.
          r0s'    = map (\r -> snd $ (filter (\(f, s) -> (take (length r) f) == r) pairs') !! 0) r0s
          r1s'    = map (\r -> snd $ (filter (\(f, s) -> (take (length r) f) == r) pairs') !! 0) r1s
          r0sprev = map prev r0s
          r1sprev = map prev r1s
          r0s''   = map (\r -> snd $ (filter (\(f, s) -> (take (length r) f) == r) pairs') !! 0) r0sprev
          r1s''   = map (\r -> snd $ (filter (\(f, s) -> (take (length r) f) == r) pairs') !! 0) r1sprev
      in zip5 from to payout (zip r0s'' r0s') (zip r1s'' r1s')
      where 
        prev s =
          let time = fromMaybe 1 (TR.readMaybe [(s !! (length s - 1) )] :: Maybe Int)
          in (take (length s - 1) s) ++ (show $ time - 1)

    print_txn ((f,t,p, (r0p, r0c), (r1p, r1c)),(sender, t0, t1)) = 
      unlines $ 
      [ sender ++ ": ---  swap(" ++ f ++ " : " ++ t0 ++ ") ---> (" ++ r0p ++ " : " ++ t0 ++ ", " ++ r1p ++ " : " ++ t1 ++ ")"
      --[ sender ++ ": ---  swap(" ++ f ++ " : " ++ t0 ++ ", " ++ t ++ " : " ++ t1 ++ ") ---> (" ++ r0p ++ " : " ++ t0 ++ ", " ++ r1p ++ " : " ++ t1 ++ ")"
      , sender ++ ": <--- receives(" ++ p ++ " : " ++ t1 ++ ") --- (" ++ r0c ++ " : " ++ t0 ++ ", " ++ r1c ++ " : " ++ t1 ++ ")"
      ]
      --sender ++ ": swap(" ++ f ++ " : " ++ t0 ++ ", " ++ t ++ " : " ++ t1 ++ ") <---" ++ p
  
-- takes as input a model output, and splits it into sub-terms
toTerms :: String -> [(String, String)]
toTerms model = 
  let model'  = map (\c -> if c == '\n' then ' ' else c) model
      model'' = drop 1 (dropWhile (/= '(') model') 
      model''' = reverse $ drop 1 (dropWhile (/= ')') $ reverse model'') 
      splitted = splitPars model''' []
      names    = map (\e -> (words e) !! 1) splitted
      vals     = map (\e -> unwords . (drop 4) $ words e) splitted
  in zip names vals
  where 
    splitPars s acc | all (flip elem "\t\n ") s = acc
    splitPars s acc = 
      let terms = dropWhile (/= '(') s
          (term, rest) = readUntilMatchPar (drop 1 terms) 1 []
      in (splitPars rest (term : acc))
    readUntilMatchPar ('(' : rest) depth acc = readUntilMatchPar rest (depth + 1) (acc ++ "(")
    readUntilMatchPar (')' : rest) depth acc | depth == 1 = (acc, rest)
    readUntilMatchPar (')' : rest) depth acc = readUntilMatchPar rest (depth - 1) (acc ++ ")")
    readUntilMatchPar (c : rest) depth acc = readUntilMatchPar rest depth (acc ++ [c])
