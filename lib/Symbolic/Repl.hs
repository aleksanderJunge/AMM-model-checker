{-# LANGUAGE LambdaCase #-}

module Symbolic.Repl where

import Symbolic.Interpreter.Parser
import Symbolic.Interpreter.SymTab
import Symbolic.Sem
import Symbolic.SMT
import Symbolic.Utils
import Data.Maybe
import Data.Char
import Data.List
import Data.Either
import Data.Tuple.Extra
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
  (stab', toknames) <- toks_ symtab 
  depth <- getDepth
  (stab'', stmts, amms, users) <- init_ stab' [] [] []
  let useFee      = any (\(SAMM _ _ _ fee) -> case fee of None -> False; _ -> True) amms
      defaultFees = if useFee then setDefaultFees amms [] else []
  (constraints) <- constrain stab'' []
  let combs  =  getCombinations useFee (amms, users) depth
      to_maximize = find (\case MAX exp _ -> True; _ -> False) constraints
  case to_maximize of 
    Just (MAX exp _) -> do
      let queries' = filter (\case MAX _ _ -> False; _ -> True) constraints
      check_and_max stab'' (buildSMTQuery (amms,users,(stmts ++ defaultFees)) useFee stab'' toknames) queries' exp [0..depth] combs
      return ()
    _ -> do
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
        'M':'A':'X':s -> 
          case parse stab s of
            Right exp -> do 
              case get stab "exp_to_maximize" of
                Just _  -> do {putStrLn "error: the name exp_to_maximize already exists in symtab!"; constrain stab acc}
                Nothing -> do
                  let stab' = bind stab ("exp_to_maximize", Symval)
                  constrain stab' (acc ++ [MAX exp (LReal 0)])
            Left e    -> do {putStrLn e; constrain stab acc}
        'E':'N':'D':s -> return acc
        _        -> constrain stab acc

    check buildQuery [] guesses = pure Nothing
    check buildQuery ks []      = pure Nothing 
    check buildQuery (k:ks) (guess:guesses) = do
        res <- check_at_depth buildQuery k guess
        case res of 
            Nothing  -> check buildQuery ks guesses
            Just (out, txs) -> pure $ Just (k, liftM snd out, txs)
    check_at_depth buildQuery k guesses = do
        txRes <- findM (\x -> liftM fst $ check_sat buildQuery k x) guesses
        case txRes of 
            Nothing -> do 
                putStrLn $ "No solution found at depth: " ++ (show k)
                pure Nothing
            Just txs -> pure . Just $ (check_sat buildQuery k txs, txs) -- TODO: optimize to not run sat on this twice!
    check_sat buildQuery k guess = do
        writeFile "/tmp/check_goal.smt2" (case buildQuery guess k of {Left e -> error e; Right r -> r})
        (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
        case take 3 stdout of
            "sat"     -> pure (True, stdout)
            otherwise -> pure (False, stderr)

    check_and_max stab buildQuery queries to_maximize [] guesses = pure Nothing
    check_and_max stab buildQuery queries to_maximize ks []      = pure Nothing 
    check_and_max stab buildQuery queries to_maximize (k:ks) (guess:guesses) = do
        res <- check_depth_and_max buildQuery queries to_maximize k guess
        case res of 
            Nothing  -> do 
              putStrLn $ "No solution found at depth " ++ (show k)
              check_and_max stab buildQuery queries to_maximize ks guesses
            Just ((lo,hi), out, txs) -> do
              putStrLn $ "Solution found at depth " ++ (show k) ++ " with max value in interval:\n[" ++ (show lo) ++ "; " ++ (show hi) ++ "]"
              let ftpr0r1  = read_model stab txs out
                  model'  = zip ftpr0r1 txs
                  to_print = map print_txn model'
                  amms     = pair_amms_tx stab txs
              mapM putStrLn to_print
              check_and_max stab buildQuery queries to_maximize ks guesses

    check_depth_and_max buildQuery queries to_maximize k guesses = do
        intervals <- mapM (\guess -> find_interval buildQuery queries to_maximize k (Nothing, Nothing) guess) guesses
        --let sat_queries' = filter (isJust . fst) (map (\(x,y,z) -> (y,z)) (filter fst3 intervals))
        --    sat_queries = map (\(x,y) -> (fromJust x, y)) sat_queries'
        --    max_val     = foldl max 0 (map (snd . fst) sat_queries )
        let max_val'    = foldl max (Just 0) (map (liftM fst . snd3) (filter fst3 intervals)) -- lower bound more important than upper bound, thus selecting max lo
        if null max_val' then pure Nothing else 
          let max_val = fromJust max_val'
              max_index = findIndex (\(_, lh, _) -> if isJust lh then (fst $ fromJust lh) == max_val else False) intervals
              --max_indices = (find (\((lo, hi), out) -> hi == max_val) sat_queries, findIndex (\((lo, hi), out) -> hi == max_val) sat_queries)
          in case max_index of 
            (Just i) -> 
              let ((lo,hi), out) = (\(b, lh, out) -> (fromJust lh, out)) (intervals !! i)
              in pure $ Just ((lo,hi), out, guesses !! i)
            _ -> pure Nothing
        where 
          find_interval buildQuery queries to_maximize k (Just lo, Just hi) guess -- TODO: consider rearranging params so (lo,hi) at back, and partially apply rest
            | lo / hi >= 0.99 = do
                let maxQuery = MAX to_maximize (LReal . toRational $ lo)
                res <- check_sat_and_max (buildQuery (maxQuery : queries)) k guess 
                --(True, (lo, hi), )
                case res of 
                  (True, Just maxval, out) -> pure (True, Just (maxval, hi), out)
                  (_, _, out) -> do -- Try again, as 'lo' might actually have been the max value, in which case exp_to_max > lo -> unsat
                    let maxQuery' = MAX to_maximize (LReal . toRational $ lo - 1 / 1e30) -- subtract small number
                    res' <- check_sat_and_max (buildQuery (maxQuery' : queries)) k guess 
                    case res' of 
                      (True, Just maxval, out) -> pure (True, Just (maxval, maxval), out) -- should be maxval exactly in this case
                      (_, _, out) -> pure (False, Nothing, out) -- Otherwise Just fail TODO: find better solution / informative message here
                    
            | otherwise = do
                let mid      = toRational $ lo + (hi - lo)/2
                    maxQuery = MAX to_maximize (LReal mid)
                res <- check_sat_and_max (buildQuery (maxQuery : queries)) k guess 
                case res of
                  (True, Just maxval, out) -> find_interval buildQuery queries to_maximize k (Just mid, Just hi) guess --upper half
                  _ -> find_interval buildQuery queries to_maximize k (Just lo, Just mid) guess --lower half
                    
          find_interval buildQuery queries to_maximize k (Just lo, Nothing) guess = do
                let hi      = lo * 2
                    maxQuery = MAX to_maximize (LReal hi)
                res <- check_sat_and_max (buildQuery (maxQuery : queries)) k guess 
                case res of
                  (True, Just maxval, out) -> find_interval buildQuery queries to_maximize k (Just hi, Nothing) guess
                  _ -> find_interval buildQuery queries to_maximize k (Just lo, Just hi) guess
            
          find_interval buildQuery queries to_maximize k (Nothing, Nothing) guess = do
            let maxQuery = MAX to_maximize (LReal 0)
            res <- check_sat_and_max (buildQuery (maxQuery : queries)) k guess 
            case res of
              (True, Just maxval, out) ->
                find_interval buildQuery queries to_maximize k (Just maxval, Nothing) guess
              (_, _, out) -> pure (False, Nothing, out)


    check_sat_and_max buildQuery k guess = do
        --putStrLn $ "checking " ++ (show guess)
        writeFile "/tmp/check_goal.smt2" (case buildQuery guess k of {Left e -> error e; Right r -> r})
        (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
        case take 3 stdout of
            "sat"     -> do 
              let pairs  = toTerms stdout
                  pairs' = filter (\(f, s) -> not $ null f || null s) pairs
                  maxval = listToMaybe . map snd $ filter (\(f, s)-> (take 15 f) == "exp_to_maximize") pairs'
              case stringToRational <$> maxval of
                Just r  -> pure (True, r, stdout)
                -- TODO: remove this trace
                Nothing -> trace "error: couldn't read exp_to_maximize as a rational!" pure (False, Nothing, stderr)
            otherwise -> pure (False, Nothing, stderr)

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
      let pairs  = toTerms model
          pairs' = filter (\(f, s) -> not $ null f || null s) pairs
          from    = map snd . sort $ (filter (\(f, s)-> (take 4 f) == "from") pairs')
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