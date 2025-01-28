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
import Data.Ratio
import Numeric
import Data.Tuple.Extra
import Data.Either.Extra
import qualified Data.Map as M
import qualified GHC.Utils.Misc as Util
import qualified Text.Read as TR
import System.IO
import System.IO.Error
import System.Process ( readProcessWithExitCode )
import Control.Monad
import Control.Monad.Extra

repl :: IO (Either String ())
repl = do
  let symtab = empty :: Env String SType
  tok_and_opts <- toks_ symtab []
  case tok_and_opts of 
    Left e -> return $ Left e
    Right (stab', toknames, opts) -> do
      depth' <- getDepth
      case depth' of
        Left e -> return $ Left e
        Right depth -> do
          amm_and_user_decls <- init_ stab' [] [] []
          case amm_and_user_decls of
            Left e -> return $ Left e
            Right (stab'', stmts, amms, users, line, txconsts) -> do
              let useFee        = any (\(SAMM _ _ _ fee) -> case fee of None -> False; _ -> True) amms
                  defaultFees   = if useFee then setDefaultFees amms [] else []
                  usingRational = not . null $ find (\case Precision Nothing -> True; _ -> False) opts
                  outputTex     = not . null $ find (\case Tex -> True; _ -> False) opts
              if usingRational && isJust txconsts then return . Left $ "Must use decimal numbers when adding constraints on transactions"
              else do 
                constraints' <- constrain stab'' line []
                case constraints' of
                  Left e -> return $ Left e
                  Right constraints -> do
                    let combs' =  getCombinations' useFee (amms, users) txconsts depth
                    if isLeft combs' then return . Left $ fromLeft' combs'
                    else do 
                      let combs = fromRight' combs'
                          to_maximize = find (\case MAX _ _ -> True; _ -> False) constraints
                      case to_maximize of 
                        Just (MAX exp _) | usingRational -> return . Left $ "Must use decimal numbers when using the 'MAX' <exp> constraint"
                        Just (MAX exp _) -> do
                          let queries' = filter (\case MAX _ _ -> False; _ -> True) constraints
                              precision = fromMaybe (Precision $ Just 3) (find (\case Precision (Just i) -> True; _ -> False) opts) 
                          check_and_max precision stab'' (buildSMTQuery opts (amms,users,(stmts ++ defaultFees)) useFee stab'' toknames) queries' exp outputTex [0..depth] combs
                          return $ Right ()
                        _ -> do
                            satResult <- check (buildSMTQuery opts (amms,users,(stmts ++ defaultFees)) useFee stab'' toknames constraints) [0..depth] combs
                            case satResult of
                                Nothing -> do {hPutStr stderr "\r\ESC[KNo solution found\n"; return $ Right ()}
                                res@(Just (depth, model, txs)) -> do
                                    hPutStr stderr $ "\r\ESC[KSolution found at depth " ++ (show depth) ++ "\n"
                                    model' <- model
                                    if outputTex then do
                                      let ftpfr0r1  = read_model stab'' txs model'
                                          model''  = zip3 ftpfr0r1 txs [1..depth]
                                          top_row_tex = create_row $ map (\(_,  _, _, iams, iusrs, _, _) -> (iams, iusrs)) ftpfr0r1 
                                          bot_row_tex = create_row $ map (\(_,  _, _, _, _, fams, fusrs) -> (fams, fusrs)) ftpfr0r1 
                                          txn_seq_tex = map create_seqs_tex model''
                                      putStrLn create_header_tex
                                      putStrLn top_row_tex
                                      putStrLn create_sep1_tex
                                      mapM putStrLn txn_seq_tex
                                      putStrLn create_sep2_tex
                                      putStrLn bot_row_tex
                                      putStrLn create_footer_tex
                                      return $ Right ()
                                    else do
                                      let ftpfr0r1  = read_model stab'' txs model'
                                          model''  = zip3 ftpfr0r1 txs [1..depth]
                                          to_print = map print_txn model''
                                      mapM putStrLn to_print
                                      return $ Right ()

  where
    toks_ stab opts = do
      line <- getLine
      case TR.readMaybe line :: Maybe SToks of 
        Just toks -> do
            case declToks toks stab of
                Left e -> return $ Left e
                Right (stab', toklst) -> do 
                    if length (nub toklst) /= length toklst then return . Left $ "duplicate token..."
                    else return . Right $ (stab', toklst, opts)
        Nothing -> 
          case TR.readMaybe line :: Maybe Opt of
            Just opt -> toks_ stab (opts ++ [opt])
            Nothing  -> 
              if isPrefixOf "--" line || all (flip elem "\t\n ") line then toks_ stab opts else
              return . Left $ "couldn't parse: \n" ++ line ++ "\nas 'TOKENS' or 'SETOPT'"

    getDepth = do
      line <- getLine
      case line of 
        _ | isPrefixOf "DEPTH" line -> 
          case TR.readMaybe (drop 5 line) :: Maybe Int of 
            Just i -> return $ Right i
            Nothing -> return $ Left "Please enter an Int as depth"
        _ | all (flip elem " \t") line || isPrefixOf "--" line -> getDepth -- Just a whitespace line
        _ -> return $ Left "Please input the DEPTH <i> to check, after the TOKENS decl"

    init_ stab stmts amms users = do
      line <- getLine
      if any (flip isPrefixOf line) ["EU", "EF", "MAX", "INIT"] then return $ Right (stab, stmts, amms, users, line, Nothing)
      else if isPrefixOf "REQUIRED" line
           || isPrefixOf "FREE" line
           || isPrefixOf "AVAILABLE" line then constrain_txs line (stab, stmts, amms, users) ([],[],[])
      else case TR.readMaybe line :: Maybe SAMM of
        Just samm -> do
          case makeAmm samm stab of
            Left e -> return $ Left e
            Right (r, stab') -> init_ stab' (stmts ++ r) (samm : amms) users
        Nothing ->
            case TR.readMaybe line :: Maybe SUser of 
            Just user ->
                case makeUser user stab of
                Left e -> return $ Left e
                Right (r, stab') -> do 
                    init_ stab' (stmts ++ r) amms (user : users)
            Nothing -> if all (flip elem "\t\n ") line || isPrefixOf "--" line
                       then init_ stab stmts amms users 
                       else return . Left $ "failed to parse: " ++ line

    constrain_txs line decs@(stab, stmts, amms, users) txcons@(reqs, avails, frees) = do
      case line of
        _ | isPrefixOf "FREE" line -> 
          case TR.readMaybe line :: Maybe TxFree of
            Just (TxFree names) ->
              if (not . null) frees then return . Left $ "error, FREE (...) already declared"
              else do
                nextLine <- getLine
                constrain_txs nextLine decs (reqs, avails, names)
            Nothing -> putError line decs txcons
        _ | isPrefixOf "AVAILABLE" line ->
          case TR.readMaybe (drop 9 line) :: Maybe TxCon of
            Just txcon -> do
              nextLine <- getLine
              constrain_txs nextLine decs (reqs, avails ++ [txcon], frees)
            Nothing -> putError line decs txcons
        _ | isPrefixOf "REQUIRED" line ->
          case TR.readMaybe (drop 8 line) :: Maybe TxCon of
            Just txcon -> do
              nextLine <- getLine
              constrain_txs nextLine decs (reqs ++ [txcon], avails, frees)
            Nothing -> putError line decs txcons
        _ | any (flip isPrefixOf line) ["EU", "EF", "MAX", "INIT"]  -> return $ Right (stab, stmts, amms, users, line, Just txcons)
        _ | isPrefixOf "--" line || all (flip elem "\n\t ") line-> do {l <- getLine; constrain_txs l decs txcons}
        _ -> putError line decs txcons
      where
        putError line tup consts = return . Left $ "error: couldn't parse: " ++ show line

    constrain stab line acc = do
      case line of --replace with guards
        'I':'N':'I':'T':s -> 
          if any (\case INIT _ -> True; _ -> False) acc then return . Left $ "Only 1 INIT line is supported (conjunctions '&&' can be used to add more constraints)"
          else case parse stab s of
            Right (exp, t) | t == TBool -> do {line' <- getLineCheckEOF; constrain stab line' (acc ++ [INIT exp])}
            Right (exp, t) | t == TRational -> return . Left $ "The output of the constraint:\n" ++ (show line) ++ "\nis a rational, but expected bool"
            Left e    -> return . Left $ e
        'E':'F':s   ->
          if any (\case EF _ -> True; EU _ _ -> True; _ -> False) acc then return . Left $ "Only 1 EF / EU query at a time is supported"
          else case parse stab s of
            Right (exp, t) | t == TBool -> do {line' <- getLineCheckEOF; constrain stab line' (acc ++ [EF exp])}
            Right (exp, t) | t == TRational -> return . Left $ "The output of the constraint:\n" ++ (show line) ++ "\nis a rational, but expected bool"
            Left e    -> return . Left $ e
        'E':'U':s   ->
          if any (\case EF _ -> True; EU _ _ -> True; _ -> False) acc then return . Left $ "Only 1 EF / EU query at a time is supported"
          else 
          let (blank1, rest1) = readUntil '(' s
              (exp1,   rest2) = readUntil ')' rest1
              (blank2, rest3) = readUntil '(' rest2
              (exp2, _)       = readUntil ')' rest3
          in if any ((==) "!") [blank1, exp1, blank2, exp2] 
             then return . Left $ "failed reading EU, syntax is: EU (exp1) (exp2)" 
             else case parse stab exp1 of
               Right (_, t) | t == TRational -> return . Left $ "The output of the constraint:\n" ++ (show line) ++ "\nis a rational, but expected bool"
               Right (exp1, t1) | t1 == TBool ->
                 case parse stab exp2 of
                   Right (_, t) | t == TRational -> return . Left $ "The output of the constraint:\n" ++ (show line) ++ "\nis a rational, but expected bool"
                   Right (exp2, t2) | t2 == TBool -> do {line' <- getLineCheckEOF; constrain stab line' (acc ++ [EU exp1 exp2])}
                   Left e -> return . Left $ "failed to parse second expression: " ++ e
               Left e    -> return . Left $ "failed to parse first expression: " ++ e
        'M':'A':'X':s -> 
          if any (\case MAX _ _ -> True; _ -> False) acc then return . Left $ "Only 1 MAX-imization constraint is supported"
          else case parse stab s of
            Right (_, t) | t == TBool -> return . Left $ "The output of the maximization constraint:\n" ++ (show line) ++ "\nis a bool, but expected a rational"
            Right (exp, t) | t == TRational -> do 
              case get stab "exp_to_maximize" of
                Just _  -> return . Left $ "error: the name exp_to_maximize already exists in symtab!"
                Nothing -> do
                  let stab' = bind stab ("exp_to_maximize", Symval)
                  line' <- getLineCheckEOF
                  constrain stab' line' (acc ++ [MAX exp Nothing])
            Left e    -> return $ Left e
        'E':'N':'D':s -> return $ Right acc
        _ | isPrefixOf "--" line || all (flip elem "\t\n ") line -> do {line' <- getLineCheckEOF; constrain stab line' acc}
        _ -> return . Left $ "failed to parse: " ++ line
        where getLineCheckEOF = catchIOError getLine (\e -> if isEOFError e then return "END" else ioError e)

    check buildQuery [] guesses = pure Nothing
    check buildQuery ks []      = pure Nothing 
    check buildQuery (k:ks) (guess:guesses)
      | null guess = do 
        hPutStr stderr $ "\r\ESC[KNo transaction combinations to create valid sequence at depth: " ++ show k ++ "\n"
        check buildQuery ks guesses
      | otherwise = do
        res <- check_at_depth buildQuery k guess
        case res of 
            Nothing  -> check buildQuery ks guesses
            Just (out, txs) -> pure $ Just (k, liftM snd out, txs)
    check_at_depth buildQuery k guesses = do
        txRes <- findM (\(x,i) -> liftM fst $ check_sat buildQuery k (i,(length guesses)) x) (zip guesses [1..length guesses])
        case txRes of 
            Nothing -> do 
                hPutStr stderr $ "\r\ESC[KNo solution found at depth: " ++ (show k) ++ "\n"
                pure Nothing
            Just (txs,_) -> pure . Just $ (check_sat buildQuery k (0,0) txs, txs) -- TODO: optimize to not run sat on this twice!
    check_sat buildQuery k (0,0) guess = check_sat' buildQuery k guess
    check_sat buildQuery k (i,m) guess = do
        hPutStr stderr $ "\r\ESC[Kchecking: " ++ show i ++ " / " ++ show m
        check_sat' buildQuery k guess
    check_sat' buildQuery k guess = do
        writeFile "/tmp/check_goal.smt2" (case buildQuery guess k of {Left e -> error e; Right r -> r})
        (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
        case take 3 stdout of
            "sat"     -> pure (True, stdout)
            otherwise -> pure (False, stderr)

    check_and_max precision stab buildQuery queries to_maximize outputTex [] guesses = pure Nothing
    check_and_max precision stab buildQuery queries to_maximize outputTex ks []      = pure Nothing 
    check_and_max precision stab buildQuery queries to_maximize outputTex (k:ks) (guess:guesses) 
      | null guess = do 
          hPutStr stderr $ "\r\ESC[KNo transaction combinations to create valid sequence at depth: " ++ show k ++ "\n"
          check_and_max precision stab buildQuery queries to_maximize outputTex ks guesses
      | otherwise = do
        res <- check_depth_and_max buildQuery queries to_maximize k guess
        let precision' = (\case Precision (Just i) -> i; _ -> 3) precision
        case res of 
            Nothing  -> do 
              hPutStr stderr $ "\r\ESC[KNo solution found at depth " ++ (show k) ++ "\n"
              check_and_max precision stab buildQuery queries to_maximize outputTex ks guesses
            Just ((lo,hi), out, txs) -> do
              hPutStr stderr $ "\r\ESC[KSolution found at depth " ++ (show k) ++ " with max value in interval: [" ++ (display precision' lo) ++ "; " ++ (display precision' hi) ++ "]\n"
              if outputTex then do
                let ftpfr0r1  = read_model stab txs out
                    model''  = zip3 ftpfr0r1 txs [1..k]
                    top_row_tex = create_row $ map (\(_,  _, _, iams, iusrs, _, _) -> (iams, iusrs)) ftpfr0r1 
                    bot_row_tex = create_row $ map (\(_,  _, _, _, _, fams, fusrs) -> (fams, fusrs)) ftpfr0r1 
                    txn_seq_tex = map create_seqs_tex model''
                putStrLn create_header_tex
                putStrLn top_row_tex
                putStrLn create_sep1_tex
                mapM putStrLn txn_seq_tex
                putStrLn create_sep2_tex
                putStrLn bot_row_tex
                putStrLn create_footer_tex
                check_and_max precision stab buildQuery queries to_maximize outputTex ks guesses
              else do
                let ftpfr0r1  = read_model stab txs out
                    model''  = zip3 ftpfr0r1 txs [1..k]
                    to_print = map print_txn model''
                mapM putStrLn to_print
                check_and_max precision stab buildQuery queries to_maximize outputTex ks guesses
        where
            display n x = (showFFloat (Just n) $ fromRat x) ""

    check_depth_and_max buildQuery queries to_maximize k guesses = do
        let maxQuery = MAX to_maximize Nothing
        satSet <- mapM (\(g,i) -> check_sat_and_max (buildQuery (maxQuery : queries)) k (i, length guesses, Nothing) g) (zip guesses [1.. length guesses])
        let satSetI = zip satSet guesses
            satVals     = (filter (fst3 . fst) satSetI)
            toCheck = (map snd satVals)
        gt0s <- mapM (\(g,i)->check_sat_and_max (buildQuery ((MAX to_maximize (Just $ LReal 0)) : queries)) k (i, length guesses, Just . show . LReal $ 0) g) (zip toCheck ([1.. length toCheck]))
        let withIndices' = zip gt0s (map snd satVals)
            (gt0, lteq0)   = partition (fst3 . fst) withIndices'
            (candidates) = if null gt0 then satVals else gt0
            lo = maximum (map (snd3 . fst) candidates) -- lower bound known so far
        if null gt0 then do
          maybeInterval <- bin_search buildQuery queries to_maximize k (fromJust lo, 0) (map snd satVals) -- TODO: check fromJust here?
          case maybeInterval of
            Just ((b, Just lh, out), txs) -> pure $ Just (lh, out, txs)
            _ -> pure Nothing
        else do 
          maybeBounds <- find_loose_bounds buildQuery queries to_maximize k lo (map snd gt0)
          case maybeBounds of
            Nothing -> pure Nothing
            Just ((lo, hi), txs) -> do
              maybeInterval <- bin_search buildQuery queries to_maximize k (lo, hi) txs
              case maybeInterval of
                Just ((b, Just lh, out), txs) -> pure $ Just (lh, out, txs)
                _ -> pure Nothing

        where 
          find_loose_bounds buildQuery queries to_maximize k Nothing guesses = pure Nothing
          find_loose_bounds buildQuery queries to_maximize k (Just lo) guesses = do
            let maxQuery = MAX to_maximize (Just . LReal $ lo * 2)
            satSet <- mapM (\(g,i) -> check_sat_and_max (buildQuery (maxQuery : queries)) k (i, length guesses, Just . show . LReal $ lo*2) g) (zip guesses [1..length guesses])
            let satSetI = zip satSet guesses
                satVals = (filter (fst3 . fst) satSetI)
            if null satVals then pure $ Just ((lo, lo * 2), guesses) else
              find_loose_bounds buildQuery queries to_maximize k (Just $ lo * 2) (map snd satVals)
          
          bin_search buildQuery queries to_maximize k (lo, hi) guesses
            | if hi == 0 then abs lo <= 0.01 else 
              if lo < 0 then 0.995 * abs lo <= abs hi else lo/hi >= 0.995 = do
                results <- mapM (get_final_interval buildQuery queries to_maximize k (lo, hi)) guesses
                let resultsI = zip results guesses
                case filter (fst3 . fst) resultsI of
                  xs | not $ null xs -> 
                    let maxv = maximum (map (snd3 . fst) resultsI)
                    in pure $ find (\((_, lh, _), _) -> lh == maxv) resultsI
                  [] -> pure Nothing
            | otherwise = do
                let mid      = toRational $ lo + (hi - lo)/2
                    maxQuery = MAX to_maximize (Just $ LReal mid)
                satSet <- mapM (\(g,i) -> check_sat_and_max (buildQuery (maxQuery : queries)) k (i, length guesses, Just . show . LReal $ mid) g) (zip guesses [1.. length guesses])
                let satSetI = zip satSet guesses
                    (sat, unsat) = partition (fst3 . fst) satSetI
                if null sat then bin_search buildQuery queries to_maximize k (lo, mid) (map snd unsat)
                else bin_search buildQuery queries to_maximize k (mid, hi) (map snd sat)
            where
              get_final_interval buildQuery queries to_maximize k (lo, hi) guess = do
                let maxQuery = MAX to_maximize (Just . LReal . toRational $ lo)
                res <- check_sat_and_max' (buildQuery (maxQuery : queries)) k guess 
                case res of 
                  (True, Just maxval, out) -> pure (True, Just (maxval, hi), out)
                  (_, _, out) -> do -- Try again, as 'lo' might actually have been the max value, in which case exp_to_max > lo -> unsat
                    let maxQuery' = MAX to_maximize (Just . LReal . toRational $ lo - 1 / 1e30) -- subtract small number
                    res' <- check_sat_and_max' (buildQuery (maxQuery' : queries)) k guess 
                    case res' of 
                      (True, Just maxval, out) -> pure (True, Just (maxval, maxval), out) -- should be maxval exactly in this case
                      (_, _, out) -> pure (False, Nothing, out) -- Otherwise Just fail TODO: find better solution / informative message here

    check_sat_and_max buildQuery k (i,m, v) guess = do
        hPutStr stderr $ "\r\ESC[Kchecking: " ++ show i ++ " / " ++ show m ++ " paths, checking value: " ++ (fromMaybe "none" v)
        check_sat_and_max' buildQuery k guess
    check_sat_and_max' buildQuery k guess = do
        --hPutStr stderr "\r\ESC[Kchecking " ++ (show guess)
        writeFile "/tmp/check_goal.smt2" (case buildQuery guess k of {Left e -> error e; Right r -> r})
        (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
        case take 3 stdout of
            "sat"     -> do 
              let pairs  = toTerms stdout
                  pairs' = filter (\(f, s) -> not $ null f || null s) pairs
                  val = listToMaybe . map snd $ filter (\(f, s)-> (take 15 f) == "exp_to_maximize") pairs'
              case liftM stringToRational val of
                Just r  -> pure (True, r, stdout)
                Nothing -> error "couldn't read exp_to_maximize as a rational!"
            otherwise -> pure (False, Nothing, stderr)

    pair_vars_to_txn stab txns = 
      let amms  = filter (\(k,v) -> case v of DAmm _ _ -> True; _ -> False) (M.toList stab)
          k = show $ length txns
          users = map (\(TxCon n _ _ _ _) -> n) txns
          tokenUniverse = map fst $ filter (\(k,v) -> case v of DTok -> True; _ -> False) (M.toList stab)
          init_users  = map (\(u, toks) -> (map (\t -> (u +@ t +@ "0", t, u)) toks))  (zip users (replicate (length users) tokenUniverse)) -- e.g. a_t0_0 : t0
          final_users = map (\(u, toks) -> (map (\t -> (u +@ t +@ k, t, u)) toks))  (zip users (replicate (length users) tokenUniverse)) -- e.g. a_t0_k : t0
          pairs = map (\(TxCon _ t0 t1 _ _) -> find (\case {(k, DAmm t0' t1') -> (t0' == t0 && t1' == t1) || 
                                                                                 (t0' == t1 && t1' == t0); _ -> False}) amms) txns
          unjust = catMaybes pairs
      in if length pairs /= length unjust then Left "one amm pair not found" else 
      let unwrapped = catMaybes $ map (\case {(n, DAmm t0 t1) -> return (n, t0, t1); _ -> Nothing}) unjust
          senders   = map (\(TxCon n t0 t1 _ _) -> (n, t0, t1)) txns
          amm_names = zipWith3 (\(n, t0, t1) (TxCon _ t0' t1' _ _) i -> 
            if t0 == t0' then ("l" +@ n +@ i, "r" +@ n +@ i, "fee" +@ n, n) else ("r" +@ n +@ i, "l" +@ n +@ i, "fee" +@ n, n)) 
              unwrapped txns (map show [1..(length txns)])
          init_amms  = map (\(n, t0, t1) -> ("l" +@ n +@ "0", "r" +@ n +@ "0", t0, t1, n))  unwrapped -- e.g. (l_t0_0, r_t1_0, t0, t1, t0t1)
          final_amms = map (\(n, t0, t1) -> ("l" +@ n +@ k, "r" +@ n +@ k, t0, t1, n))  unwrapped -- e.g. (l_t0_k, r_t1_k, t0, t1, t0t1)
          user_names = zipWith (\(n, t0, t1) i -> (n +@ t0 +@ i, n +@ t1 +@ i)) senders (map show [1..(length txns)])
      in return (unzip4 amm_names, unzip user_names, unzip5 init_amms, init_users, unzip5 final_amms, final_users)
    
    read_model stab txs model =
      let pairs  = toTerms model
          pairs' = filter (\(f, s) -> not $ null f || null s) pairs
          from    = map snd . sort $ (filter (\(f, s)-> (take 4 f) == "from") pairs')
          to      = map snd . sort $ (filter (\(f, s)-> (take 2 f) == "to") pairs')
          payout  = map snd . sort $ (filter (\(f, s)-> (take 6 f) == "payout") pairs')
          ((r0s, r1s, fees, ns), (froms, tos), (ls, rs, t0s, t1s, ammkey), iusers, (fls, frs, ft0s, ft1s, fammkey), fusers) 
            = fromRight' $ pair_vars_to_txn stab txs -- TODO: make better error handling here, also below.
          --(init_users, init_amms, updated_wals) = if tex_mode then read_vars_for_tex stab txs else ([], [])
          --init_amms = 
          (init_ls, init_rs, init_ns) = (getval ls pairs', getval rs pairs', ammkey)
          (final_ls, final_rs, final_ns) = (getval fls pairs', getval frs pairs', fammkey)
          init_users = map (\wal -> (getval (map fst3 wal) pairs', map snd3 wal, map thd3 wal)) iusers 
          final_users = map (\wal -> (getval (map fst3 wal) pairs', map snd3 wal, map thd3 wal)) fusers 
          r0sprev    = map prev r0s
          r1sprev    = map prev r1s
          fromsprev  = map prev froms
          tosprev    = map prev tos
          tosprev'   = getval tosprev pairs'
          fromsprev' = getval fromsprev pairs'
          tos'       = getval tos pairs'
          froms'     = getval froms pairs'
          r0s'       = getval r0s pairs'
          r1s'       = getval r1s pairs'
          r0sprev'   = getval r0sprev pairs'
          r1sprev'   = getval r1sprev pairs'
          fees'   = map (\r -> filter (\(f, _) -> (take (length r) f) == r) pairs') fees
          fees''  = if any null fees' then replicate (length txs) "0" else map (snd . (!! 0)) fees'
      in zip7 (zip4 from to payout fees'') (zip4 r0sprev' r0s' r1sprev' r1s') (zip4 fromsprev' froms' tosprev' tos') 
              (zip5 init_ls init_rs t0s t1s init_ns) init_users (zip5 final_ls final_rs ft0s ft1s final_ns) final_users
      where 
        prev s =
          let time = fromMaybe 1 (TR.readMaybe [(s !! (length s - 1) )] :: Maybe Int)
          in (take (length s - 1) s) ++ (show $ time - 1)
        getval fields p = map (\field -> snd $ (filter (\(f, _) -> take (length field) f == field) p) !! 0) fields

    print_txn (((f,t,p, fee), (r0p, r0c, r1p, r1c), (frp, fr, top, to),_,_,_,_),(TxCon sender t0 t1 _ _),_) = 
      let t' = stringToRational t
          p' = stringToRational p
          (rejected, msg) = (p' < t' || t' < Just 0, if p' < t' then t ++ " > " ++ p else t ++ " < 0")
          sender_and_message = sender ++ "[" ++ frp ++ ":" ++ t0 ++ ", " ++ top ++ ":" ++ t1 ++ "]"
                                      ++ " ----swap(" ++ f ++ ":" ++ t0 ++ ", " ++ t ++ ":" ++ t1  ++ ")"
          receiver_and_message = if rejected && (not . null) t' && (not . null) p' then 
              sender ++ "[" ++ frp ++ ":" ++ t0 ++ ", " ++ top ++ ":" ++ t1 ++ "]" ++  " transaction REJECTED! as " ++ msg else
              sender ++ "[" ++ fr ++ ":" ++ t0 ++ ", " ++ to ++ ":" ++ t1 ++ "]" ++ " <---receives(" ++ p ++ ":" ++ t1 ++ ")"
          old_amm = "(" ++ r0p ++ ":" ++ t0 ++ ", " ++ r1p ++ ":" ++ t1 ++ ", " ++ fee ++ ":fee)"
          new_amm = "(" ++ r0c ++ ":" ++ t0 ++ ", " ++ r1c ++ ":" ++ t1 ++ ", " ++ fee ++ ":fee)"
          recv_padding = "---" ++ (replicate (length sender_and_message - length receiver_and_message) '-') ++ " "
          send_padding = "--" ++ (replicate (length receiver_and_message - length sender_and_message) '-') ++ "> "
      in unlines $ 
      [ sender_and_message ++ send_padding ++ old_amm
      , receiver_and_message ++ recv_padding ++ new_amm
      ]

--    write_to_tex_fig (((f,t,p, fee), (r0p, r0c), (r1p, r1c), (frp, fr, top, to),(init_ls, init_rs, t0s, t1s, init_ns),init_users),(TxCon sender t0 t1 _ _),i) = 
--                toprow_tex = create_row $ map (\(_, _, _, _, iams, iusrs) -> (iams, iusrs)) ftpr0r1 

    create_header_tex = "\\begin{figure}[ht]\\begin{sequencediagram}\n"
    create_sep1_tex = "\n\\postlevel\n\\postlevel\n\\postlevel"
    create_sep2_tex = "    \\end{sequencediagram}\n\n    \\vspace{-5.00mm} \n\n\\begin{sequencediagram}\n"
    create_footer_tex = "  \\end{sequencediagram}\n\\caption{INSERT CAPTION}\n\\label{fig:LABEL}\n\\end{figure}"

    create_row :: [((String, String, String, String, String), ([String], [String], [String]))] -> String
    create_row init_res = 
      let amms = nub $  map fst init_res
          users = nub $ map (\(vals, toks, names) -> (unwords . intersperse "," $ zipWith (\v t -> v ++ " : " ++ t) vals toks, names !! 0 )) (map snd init_res)
          back_users = take (div (length users) 2) users
          front_users  = drop (div (length users) 2) users
      in unlines $ (map create_user front_users) ++ (map create_amm amms) ++ (map create_user back_users)
      where
        create_user (wal, name) = 
          let header = "\\newthread[gray!10]{"++ name ++ "}{\\shortstack{$\\mathsf{User \\; " ++ name ++ "}$\\\\ \\\\"
              mid = "    \\begin{tikzpicture}\n            \\node [fill=gray!20,draw=black,thick ,align=center] {$[" ++ wal ++ "]$};"
              footer = "\n    \\end{tikzpicture}}}{}" in header ++ mid ++ footer
        create_amm (l, r, t0, t1, n) =
          let header = "\\newthread[gray!10]{" ++ n ++ "}{\\shortstack{$\\mathsf{AMM}\\:" ++ n ++"$\\\\ \n\\begin{tikzpicture}[shape aspect=.2]\n\\tikzset{every node/.style={cylinder, "
                      ++ "shape border rotate=90, draw,fill=gray!25}}\\node  at (2.5,0) {$\\{"
              mid = l ++ " : " ++ t0 ++ ", " ++ r ++ " : " ++ t1
              footer = "\\}$};\\end{tikzpicture}}}{}"
          in header ++ mid ++ footer

    create_seqs_tex (((f,t,p, fee), (r0p, r0c, r1p, r1c), (frp, fr, top, to),(_, _, _, _, init_ns),_, _,_),(TxCon sender t0 t1 _ _),i) = 
      let t' = stringToRational t
          p' = stringToRational p
          was_rejected = p' < t' in if was_rejected then error "rejected transaction not allowed in tex output" else
      let header = "    \\begin{messcall}{" ++ sender ++ "}{\\shortstack[c] {\n    \\postlevel\n    \\begin{tikzpicture}\\tikzset{every node/.style={fill=gray!20}}\n    \\node [copy shadow, draw=black,thick ,align=center]\n"
          swap1  = "    {$s_" ++ (show i) ++ "= \\mathsf{" ++ sender ++ "}\\colon \\swap(" ++ f ++ " : " ++ t0 ++ ", " ++ t ++ " : " ++ t1 ++ ")$\\\\"
          swap2  = "    ${\\mathsf{" ++ sender ++ "}[" ++ fr ++ " : " ++ t0 ++ ", " ++ to ++ " : " ++ t1 ++ "]}\\vert\\{" ++ r1c ++ " : " ++ t1 ++ ", " ++ r0c ++ " : " ++ t0 ++ "\\}$};"
          footer = "    \\end{tikzpicture}}}{"++ init_ns ++"}{}\\end{messcall}"
      in header ++ swap1 ++ swap2 ++ footer
  


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