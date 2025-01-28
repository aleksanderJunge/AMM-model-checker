{-# LANGUAGE LambdaCase #-}
module Symbolic.SMT where

import Symbolic.Interpreter.Parser
import Symbolic.Interpreter.SymTab
import Symbolic.Sem
import Symbolic.Utils
import Data.Maybe
import Data.List
import Data.Either
import Data.Tuple.Extra
import qualified Data.Map as M
import qualified Data.Set as S
import qualified GHC.Utils.Misc as Util
import qualified Text.Read as TR
import System.IO

data Query = EU Expr Expr | EF Expr | INIT Expr | MAX Expr (Maybe Expr)
  deriving (Show) --TODO: remove this

type Symtable = Env String SType

type TxGuess = (String, String, String)

type TxSeqGuess = [TxGuess]

buildSMTQuery :: [Opt] -> ([SAMM], [SUser], [Assert]) -> Bool -> Symtable -> [String] -> [Query] -> [TxCon] -> Int -> Either String String
buildSMTQuery _ ([], _, _) _ _ _ _ _ _ = Left "Missing AMMS"
buildSMTQuery _ (_, [], _) _ _ _ _ _ _ = Left "Missing Users"
--buildSMTQuery (_, _, _) _ _ _ [] _ _ = Left "Missing Query"
buildSMTQuery opts (samms, susers, assertions) useFee stab toks queries guess k =
    let swappingAmms = ammsToUse guess samms
        swappingUsers = usersToUse guess susers toks
        max_query     = catMaybes $ map (\case MAX exp gtval -> Just (exp, gtval); _ -> Nothing) queries
        precision     = fromMaybe (Precision $ Just 3) (find (\case Precision _ -> True; _ -> False) opts)
    in Right $
    unlines ["(set-logic QF_NRA)"]
    ++ (\case Precision Nothing -> ""; Precision (Just i) -> unlines ["(set-option :pp.decimal true)", "(set-option :pp.decimal_precision " ++ show i ++ ")"]) precision
    ++ unlines (map show (buildVars samms susers toks useFee k))
    ++ unlines (map show assertions)
    ++ posBalAssertion susers toks k
    ++ (chain swappingAmms swappingUsers useFee)
    ++ unlines (map (show . Assert . decorateWithDepth 0) [ exp | INIT exp <- queries])
    ++ unlines (map (show . Assert . decorateWithDepth k) [ exp | EF exp <- queries])
    ++ unlines (concat $ map (\(i, exps) -> map (show . Assert . decorateWithDepth i) exps) (zip [0..k-1] (replicate k [ exp1 | EU exp1 exp2 <- queries])))
    ++ unlines (map (show . Assert . decorateWithDepth k) [ exp2 | EU exp1 exp2 <- queries])
    ++ (case listToMaybe max_query of Just (tm, gv) -> buildMaxExp (decorateWithDepth k tm) (decorateWithDepth k <$> gv); _ -> [])
    ++ unlines ["(check-sat)"]
    ++ unlines ["(get-model)"]
    where
      usersToUse guesses users toks =
        go guesses users toks 1 [] 
        where 
          go [] users toks k acc = acc  -- TODO: check if we need any sort of guard on this statement
          go ((TxCon usr t0 t1 v0 v1) : guesses) users toks k acc =
            let remUsers        = map name (filter (\u -> (name u) /= usr) users)
                unchangedCombs  = [(n +@ t +@ i)| n <- remUsers, t <- toks, i <- [show k]] ++ 
                                  [(n +@ t +@ i)| n <- [usr], t <- (toks \\ [t0, t1]), i <- [show k]]
                from = (usr +@ t0 +@ (show k))
                to   = (usr +@ t1 +@ (show k))
            in go guesses users toks (k + 1) (acc ++ [(from, to, v0, v1, unchangedCombs)])
      ammsToUse guesses amms =
        go guesses amms 1 []
        where
          go [] amms k acc = acc
          go ((TxCon _ t0 t1 _ _):guesses) amms k acc =
            case find (\(SAMM _ r0' r1' _) -> ((snd $ r0') == t0 && (snd $ r1') == t1) || 
                                              ((snd $ r0') == t1 && (snd $ r1') == t0)) amms of
              Nothing -> error "no amm on this token pair" -- TODO: handle better
              Just samm@(SAMM n (_, t0') (_, t1') _) ->
                let fromVar  = (if t0' == t0 then "l" else "r") +@ n +@ (show k)
                    toVar    = (if t0' == t0 then "r" else "l") +@ n +@ (show k)
                    feeName  = "fee" +@ n
                    remNames = [(d +@ n +@ i) | d <- ["l", "r"], 
                                                n <- (map ammName (delete samm amms)),
                                                i <- [show k]]
                in go guesses amms (k + 1) (acc ++ [(feeName, fromVar, toVar, remNames)])

buildMaxExp :: Expr -> Maybe Expr -> String
buildMaxExp exp Nothing =
  let var_name = "exp_to_maximize"
  in unlines $ (map show [DeclVar var_name TReal]) ++ map show
    [ Assert $ eq (Var var_name) exp ]
buildMaxExp exp (Just gt_val) =
  let var_name = "exp_to_maximize"
  in unlines $ (map show [DeclVar var_name TReal]) ++ map show
    [ Assert $ eq (Var var_name) exp
    , Assert $ gt (Var var_name) gt_val
    ]
  
-- this could be somewhat limiting in the sense that there's no way to compare variables across different time steps in the query language
decorateWithDepth :: Int -> Expr -> Expr
decorateWithDepth k exp =
  decorate exp k 
  where 
    decorate :: Expr -> Int -> Expr
    decorate (Var n) k 
      | take 4 n  == "fee_"  = Var n --fee & maxexp remains unchanged, TODO: use symtab to do this instead of string checking
      | take 15 n == "exp_to_maximize" = Var n
      | otherwise           = Var $ n +@ show k
    decorate (LReal r) k = LReal r
    decorate (LBool b) k = LBool b
    decorate (UnOp unop e) k          = UnOp unop (decorate e k)
    decorate (BinOp binop e1 e2) k    = BinOp binop (decorate e1 k) (decorate e2 k)
    decorate (TerOp terop e1 e2 e3) k = TerOp terop (decorate e1 k) (decorate e2 k) (decorate e3 k)
    decorate exp _ = exp

getSymVals :: Symtable -> [String]
getSymVals stab =
  let vals = map fst (filter (\(k,v) -> v == Symval) (M.toList stab))
  in map (\s -> "(get-value (" ++ s ++ "))") vals

-- The new parameter contains a tuple (Req, Avail, Free) where first two elements are transactions that are req/avail and third elem is names of users who are free to transact
getCombinations' :: Bool -> ([SAMM], [SUser]) -> Maybe ([TxCon], [TxCon], [String]) -> Int -> Either String [[[TxCon]]]
getCombinations' useFee (samms, susers) txcons k =
  if isNothing txcons then Right $ getCombinations useFee (samms, susers) k else
  let (req, avail, free) = fromJust txcons
      freeTxs = k - length req
  in if freeTxs < 0 then Left "error: checking at lower depth than #(required txns)" else
  let token_pairs' = map (\(SAMM _ r0' r1' _) -> (snd r0', snd r1')) samms
      tokens        = nub . concat $ map (\(a, b) -> [a, b]) token_pairs'
      token_pairs  = S.fromList token_pairs'
      names         = map name susers
      free_names    = S.fromList free
      combinations  = [TxCon n t0 t1 Nothing Nothing | n <- names, t0 <- tokens, t1 <- tokens, t0 /= t1, 
                                                      S.member n free_names, (S.member (t0, t1) token_pairs) 
                                                      || (S.member (t1, t0) token_pairs) ]
      ks            = [0..k]
  in Right $ map (nub . getAtDepth combinations req avail) ks
  where
    getAtDepth combs req avail k =
      let num_req   = length req
          num_avail = [0..(min (length avail) (k-num_req))]
          num_free  = reverse [0 .. (k - num_req)]
          set_avail = map (choose_k avail) num_avail
          set_free = map (getGuesses' combs) (num_free)
          avail_and_free = concat $ map (\(a,f) -> concat $ map (permute' f) a) (zip set_avail set_free)
      in permute' avail_and_free req
    getGuesses' combs i = sequence $ replicate i combs
    permute' [] _ = []
    permute' combs [] = combs
    permute' combs (elm : elms) = 
      let i =  (\case h:_ -> length h + 1) combs
          ith_depth_perms = concat $ map (\(l', i) ->map (\l -> (take i l) ++ [elm] ++ (drop i l)) l') (zip (replicate i $ combs) [0..])
      in permute' ith_depth_perms elms 
    choose_k avails k = nubBy (\l l' -> all (flip elem l) l' && all (flip elem l') l) $ map (take k) $ permutations avails

getCombinations :: Bool -> ([SAMM], [SUser]) -> Int -> [[[TxCon]]]
getCombinations useFee (samms, susers) k =
  -- TODO: do more error checking here, such as checking for that length of unqieu elems = original list... etc.
  let token_pairs' = map (\(SAMM _ r0' r1' _) -> (snd r0', snd r1')) samms
      tokens        = nub . concat $ map (\(a, b) -> [a, b]) token_pairs'
      token_pairs  = S.fromList token_pairs'
      names         = map name susers
      combinations  = [TxCon n t0 t1 Nothing Nothing | n <- names, t0 <- tokens, t1 <- tokens, t0 /= t1, 
                                      (S.member (t0, t1) token_pairs) || (S.member (t1, t0) token_pairs) ]
      ks            = [0..k]
      guesses       = map (getGuesses combinations) ks
  in  if useFee then guesses else map (filter check_adjacent_txns) guesses
  where
    getGuesses combs k = sequence $ replicate k combs
    check_adjacent_txns [] = True
    check_adjacent_txns (tx:[]) = True
    check_adjacent_txns (tx:txs) = (check_tx tx txs) && check_adjacent_txns txs
        where 
            check_tx tx [] = True
            check_tx tx@(TxCon n t0 t1 _ _) txs = 
              case findIndex (\(TxCon n' t0' t1' _ _) -> n' == n && all (flip elem [t0',t1']) [t0,t1]) txs of 
                  Nothing -> True -- no identical tx found in remainder
                  Just i  -> any (\(TxCon n' t0' t1' _ _) -> 
                          (n' /= n && all (flip elem [t0',t1']) [t0,t1]) ||         -- different sender, on same AMM
                          (n' == n && not (all (flip elem [t0',t1']) [t0,t1]))) (take i txs) -- same sender, on different AMM

posBalAssertion :: [SUser] -> [String] -> Int -> String
posBalAssertion users toks k =
  let userVars = [(n +@ t +@ i) | n <- (map name users), t <- toks, i <- (map show [0..k])]
  in unlines $ map (\v -> show . Assert $ gteq (Var v) (LReal 0)) userVars

-- TODO: refactor this bs function and the one below it
createSymvals :: [SAMM] -> Symtable -> Int -> Symtable
createSymvals samms stab k =
  let r0pairs = map (\(SAMM n (v, t) (_, _) _) -> bindIfNullr stab v t n k) samms
      r1pairs = map (\(SAMM n (_, _) (v', t') _) -> bindIfNullr stab v' t' n k) samms
      stab'   = foldl (\acc st -> M.union st acc) stab r0pairs
  in  foldl (\acc st -> M.union st acc) stab' r1pairs
bindIfNullr :: Symtable -> Maybe Rational -> String -> String -> Int -> Symtable
bindIfNullr stab v t n k | null v = 
  bind stab (n +@ t +@ (show k), Symval)
bindIfNullr stab _ _ _ _ = stab

setDefaultFees :: [SAMM] -> [Assert] -> [Assert]
setDefaultFees [] acc = acc
setDefaultFees ((SAMM n (v, t) (v', t') fee):samms) acc =
  setDefaultFees samms (acc ++ (if fee == None then [Assert $ eq (Var $ "fee_" ++ n) (LReal 0) ] else []))


makeAmm :: SAMM -> Symtable -> Either String ([Assert], Symtable)
makeAmm (SAMM n (v, t) (v', t') fee) stab =
    if isJust (get stab n) then Left $ n ++ " already declared!"
    else if any (\case DAmm t0 t1 -> elem t0 [t, t'] && elem t1 [t, t']; _ -> False) (codomain stab)
    then Left $ "AMM on token pair: (" ++ t ++ " , " ++ t' ++ ") already exists!"
    else if not (checkTok stab t)  then Left $ "Token: " ++ t  ++ " doesn't exist" ++ " in stab: " ++ (show stab)
    else if not (checkTok stab t') then Left $ "Token: " ++ t' ++ " doesn't exist" ++ " in stab: " ++ (show stab)
    else 
    let assrt_v    = fromMaybe [lt (LReal 0) (Var $ "l_" ++ n +@ "0")]
                  ( v  >>= (\v -> Just [eq (LReal v)  (Var $ "l_" ++ n +@ "0")] ))
        assrt_v'   = fromMaybe [lt (LReal 0) (Var $ "r_" ++ n +@ "0")] 
                  ( v' >>= (\v -> Just [eq (LReal v)  (Var $ "r_" ++ n +@ "0")] ))
        assrt_f    = case fee of 
          Conc r -> [eq (LReal r) (Var $ "fee_" ++ n)]
          Sym    -> (gt (LReal 1) (Var $ "fee_" ++ n)) : [gteq (Var $ "fee_" ++ n) (LReal 0) ] -- default constraints for symbolic values for the fee
          None   -> []
        stab1 = bind stab (n, DAmm t t')
        --stab2 = bind stab1 ("l_" ++ n +@ "0", if null v then Symval else Concval)
        --stab3 = bind stab2 ("r_" ++ n +@ "0", if null v' then Symval else Concval)
        stab2 = if fee /= None then bind stab1 ("fee_" ++ n, if fee == Sym then Symval else Concval) else stab1
    in Right $ (map Assert (assrt_v ++ assrt_v' ++ assrt_f), stab2)
    where 
        checkTok stab tok_name =
            let tt = get stab tok_name in
            if isJust tt && (fromJust tt == DTok) then True else False

chain :: [(String, String, String, [String])] -> [(String, String, Maybe Rational, Maybe Rational, [String])] -> Bool -> String
chain amms users useFee =
  unlines $ go amms users useFee 1 []
  where
    go _ [] _ _ acc = acc
    go [] _ _ _ acc = acc
    go ((fee, t0Amm, t1Amm, uncAmm):amms) ((t0Usr, t1Usr, v0Usr, v1Usr, uncUsr):users) useFee k acc = 
      go amms users useFee (k + 1) (acc ++ ([payout_assrtn, ite_assrtn, posfrom_assrtn]) ++ unc_assrtn)
      where 
        payout_assrtn = show . Assert $ 
            if not useFee then 
              eq (Var $ "payout" +@ (show k)) 
                 (divi 
                   (mul (Var $ "from" +@ (show k)) (Var $ prev t1Amm)) 
                   (add (Var $ "from" +@ (show k)) (Var $ prev t0Amm)))
            else 
              eq (Var $ "payout" +@ (show k)) 
                 (divi 
                   (mul (mul (Var $ "from" +@ (show k)) (sub (LReal 1) (Var fee))) (Var $ prev t1Amm)) 
                   (add (mul (Var $ "from" +@ (show k)) (sub (LReal 1) (Var fee))) (Var $ prev t0Amm)))
        ite_assrtn = unlines 
          [ "(assert (ite"
          , "  (and (>= to_" ++ (show k) ++ " 0) (<= to_" ++ (show k) ++ " payout_" ++ (show k) ++ "))"
          , "  (and"
          , "    (= "++ t0Amm ++ " (+ " ++ (prev t0Amm) ++ " " ++ ("from_"   ++ (show k)) ++ "))"
          , "    (= "++ t1Amm ++ " (- " ++ (prev t1Amm) ++ " " ++ ("payout_" ++ (show k)) ++ "))"
          , "    (= "++ t0Usr ++ " (- " ++ (prev t0Usr) ++ " " ++ ("from_"   ++ (show k)) ++ "))"
          , "    (= "++ t1Usr ++ " (+ " ++ (prev t1Usr) ++ " " ++ ("payout_" ++ (show k)) ++ "))"
          , "  )"
          , "  (and"
          , "    (= "++ t0Amm ++ " " ++ (prev t0Amm) ++ ")"
          , "    (= "++ t1Amm ++ " " ++ (prev t1Amm) ++ ")"
          , "    (= "++ t0Usr ++ " " ++ (prev t0Usr) ++ ")"
          , "    (= "++ t1Usr ++ " " ++ (prev t1Usr) ++ ")"
          , "  )"
          , "))"
          ]
        posfrom_assrtn = unlines 
          [ if isNothing v0Usr then show . Assert $ gt (Var $ "from" +@ show k) (LReal 0)
            else show . Assert $ eq (Var $ "from" +@ show k) (LReal $ fromJust v0Usr)
          , if isNothing v1Usr then ""
            else show . Assert $ eq (Var $ "to" +@ show k) (LReal $ fromJust v1Usr)
          ]
        unc_assrtn = 
          let uncAmms = map (\v -> show . Assert $ eq (Var $ v) (Var $ prev v)) uncAmm
              uncUsrs = map (\v -> show . Assert $ eq (Var $ v) (Var $ prev v)) uncUsr
          in uncAmms ++ uncUsrs
    prev s =
      let time = fromMaybe 1 (TR.readMaybe [(s !! (length s - 1) )] :: Maybe Int)
      in (take (length s - 1) s) ++ (show $ time - 1)
      

buildVars :: [SAMM] -> [SUser] -> [String] -> Bool -> Int -> [Decl]
buildVars amms users toks useFee k =
  let userCombs   = [(n, t, i) | n <- (map name users), t <- toks, i <- [0..k]]
      ammCombs    = [(p, n, i) | p <- ["l", "r"], n <- (map ammName amms), i <- [0..k]]
      feeCombs    = if useFee then map ammName amms else []
      txnCombs    = [(f, i) | f <- ["payout", "from", "to"], i <- [1..k]]
      userDecls = map declUser userCombs
      ammDecls  = map declAmm ammCombs
      txnDecls  = map declTxn txnCombs
      feeDecls  = map declFee feeCombs
  in userDecls ++ ammDecls ++ txnDecls ++ feeDecls
  where
    declUser (n, tok, i)   = DeclVar (n +@ tok +@ (show i)) TReal
    declAmm (prefix, n, i) = DeclVar (prefix +@ n +@ (show i)) TReal
    declFee n              = DeclVar ("fee_" ++ n) TReal
    declTxn (field, i)     = DeclVar (field +@ (show i)) TReal


-- TODO: opt point, maybe completely concretize wallet by storing rather than selecting tokens from it 
makeUser :: SUser -> Symtable -> Either String ([Assert], Symtable)
makeUser (SUser wal n) stab =
    if isJust (get stab n) then Left $ n ++ " already declared!"
    else if any (\t -> not $ checkTok stab t) (map fst wal)  then Left $ " one or more tokens not found in: " ++ show stab
    else if length (map fst wal) /= length (nub $ map fst wal) then Left " some tokens are declared twice"
    else 
    let wal_dom   = nub $ map fst wal
        stab_dom  = nub $ map fst (filter (\(k,v) -> v == DTok) (M.toList stab))
        undef     = stab_dom \\ wal_dom -- these will be set to 0

        -- TODO: consider adding symbolic values to symtable to signify that we want to print the values given to those
        conc_wal  = Util.mapSnd fromJust (filter (\(k,v) -> isJust v) wal)
        symb_wal  = filter (\(k,v) -> isNothing v) wal
        conc_ass  = concat $ map (\(t,v) -> [eq (Var $ n +@ t ++ "_0") (LReal v)]) conc_wal
        symb_ass  = concat $ map (\(t,_) -> [gteq (Var $ n +@ t ++ "_0") (LReal 0)]) symb_wal
        undef_ass = concat $ map (\t     -> [eq (Var $ n +@ t ++ "_0") (LReal 0)]) undef
        stab' = bind stab (n, DUser)
    in Right (map Assert (conc_ass ++ undef_ass ++ symb_ass), stab')
    where 
        checkTok stab tok_name =
            let tt = get stab tok_name in
            if isJust tt && (fromJust tt == DTok) then True else False

-- given a list of names, declares these to be the set of tokens
declToks :: SToks -> Symtable -> Either String (Symtable, [String]) -- third element is the list of tokens declared (to be used in haskell for further processing)
declToks (SToks toks) stab =
    if elem DTok (codomain stab) then Left "Tokens have already been declared!" else
        let stab' = foldl (\st tok -> bind st (tok, DTok)) stab toks
        in Right (stab', toks)