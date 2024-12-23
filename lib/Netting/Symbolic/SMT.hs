{-# LANGUAGE LambdaCase #-}
module Netting.Symbolic.SMT where

import Netting.Symbolic.Interpreter.Parser
import Netting.Symbolic.Interpreter.SymTab
import Netting.Symbolic.Sem
import Netting.Symbolic.Utils
import Data.Maybe
import Data.List
import Data.Either
import Data.Tuple.Extra
import qualified Data.Map as M
import qualified Data.Set as S
import qualified GHC.Utils.Misc as Util
import qualified Text.Read as TR
import System.IO

data Query = EU Expr Expr | EF Expr | INIT Expr
  deriving (Show) --TODO: remove this

type Symtable = Env String SType

type TxGuess = (String, String, String)

type TxSeqGuess = [TxGuess]

buildSMTQuery :: ([SAMM], [SUser], [Assert]) -> Bool -> Symtable -> [String] -> [Query] -> TxSeqGuess -> Int -> Either String String
buildSMTQuery ([], _, _) _ _ _ _ _ _ = Left "No AMMS"
buildSMTQuery (_, [], _) _ _ _ _ _ _ = Left "No Users"
buildSMTQuery (samms, susers, assertions) useFee stab toks queries guess k =
    -- TODO: simplify this if we don't allow for symbolic tokens!
    let swappingAmms = ammsToUse guess samms -- contains (ammName, [ammName], dir) where first ammName is the one to swap on and second is rest
        swappingUsers = usersToUse guess susers toks
        stab'        = createSymvals samms stab k
    in Right $
    unlines ["(set-logic QF_NRA)"]
    ++ unlines (map show (buildVars samms susers toks useFee k))
    ++ unlines (map show assertions)
    ++ posBalAssertion susers toks k
    ++ (chain swappingAmms swappingUsers useFee)
    ++ unlines (map (show . decorateWithDepth 0) [ exp | INIT exp <- queries])
    ++ unlines (map (show . decorateWithDepth k) [ exp | EF exp <- queries])
    ++ unlines (concat $ map (\(i, exps) -> map (show . decorateWithDepth i) exps) (zip [0..k-1] (replicate k [ exp1 | EU exp1 exp2 <- queries])))
    ++ unlines (map (show . decorateWithDepth k) [ exp2 | EU exp1 exp2 <- queries])
    ++ unlines ["(check-sat)"]
    -- ++ showStmts (stmts ++ symdecls)
    -- ++ (chain guess swappingAmms k)
    -- ++ unlines (getSymVals stab')
    -- ++ (unlines $ map (\i -> "(get-value (txn" ++ i ++ "))") $ show <$> [1..k])
    where
      usersToUse guesses users toks =
        go guesses users toks 1 [] 
        where 
          go [] users toks k acc = acc  -- TODO: check if we need any sort of guard on this statement
          go ((usr, t0, t1) : guesses) users toks k acc =
            let remUsers        = map name (filter (\u -> (name u) /= usr) users)
                unchangedCombs  = [(n +@ t +@ i)| n <- remUsers, t <- toks, i <- [show k]] ++ 
                                  [(n +@ t +@ i)| n <- [usr], t <- (toks \\ [t0, t1]), i <- [show k]]
                from = (usr +@ t0 +@ (show k))
                to   = (usr +@ t1 +@ (show k))
            in go guesses users toks (k + 1) (acc ++ [(from, to, unchangedCombs)])
      ammsToUse guesses amms = 
        go guesses amms 1 []
        where
          go [] amms k acc = acc
          go ((_, t0, t1):guesses) amms k acc =
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

  
-- this could be somewhat limiting in the sense that there's no way to compare variables across different time steps in the query language
decorateWithDepth :: Int -> Expr -> Assert
decorateWithDepth k exp =
  Assert $ decorate exp k 
  where 
    decorate :: Expr -> Int -> Expr
    decorate (Var n) k   = (Var $ n +@ (show k))
    decorate (LReal r) k = (LReal r)
    decorate (LBool b) k = (LBool b)
    decorate (UnOp unop e) k          = UnOp unop (decorate e k)
    decorate (BinOp binop e1 e2) k    = BinOp binop (decorate e1 k) (decorate e2 k)
    decorate (TerOp terop e1 e2 e3) k = TerOp terop (decorate e1 k) (decorate e2 k) (decorate e3 k)
    decorate exp _ = exp

getSymVals :: Symtable -> [String]
getSymVals stab =
  let vals = map fst (filter (\(k,v) -> v == Symval) (M.toList stab))
  in map (\s -> "(get-value (" ++ s ++ "))") vals

getCombinations :: Bool -> ([SAMM], [SUser]) -> Int -> [[TxSeqGuess]]
getCombinations useFee (samms, susers) k =
  -- TODO: do more error checking here, such as checking for that length of unqieu elems = original list... etc.
  let token_pairs' = map (\(SAMM _ r0' r1' _) -> (snd r0', snd r1')) samms
      tokens        = nub . concat $ map (\(a, b) -> [a, b]) token_pairs'
      token_pairs  = S.fromList token_pairs'
      names         = map name susers
      combinations  = [(n, t0, t1) | n <- names, t0 <- tokens, t1 <- tokens, t0 /= t1, 
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
            check_tx tx []          = True
            check_tx tx@(n, t, t') ((n', t'', t'''):txs)
                | n == n' && ((t == t'' && t' == t''') || (t == t''' && t' == t'' )) = False
                | n /= n' && ((t == t'' && t' == t''') || (t == t''' && t' == t'' )) = True
                | otherwise = check_tx tx txs

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

-- TODO: enable parsing more numbers and check for subzero
makeAmm :: SAMM -> Int -> Symtable -> Either String ([Assert], Symtable)
makeAmm (SAMM n (v, t) (v', t') fee) depth stab =
    if isJust (get stab n) then Left $ n ++ " already declared!"
    else if not (checkTok stab t)  then Left $ "Token: " ++ t  ++ " doesn't exist" ++ " in stab: " ++ (show stab)
    else if not (checkTok stab t') then Left $ "Token: " ++ t' ++ " doesn't exist" ++ " in stab: " ++ (show stab)
    else 
    let assrt_v    = fromMaybe [lt (LReal 0) (Var $ "l_" ++ n +@ (show depth))]
                  ( v  >>= (\v -> Just [eq (LReal v)  (Var $ "l_" ++ n +@ (show depth))] ))
        assrt_v'   = fromMaybe [lt (LReal 0) (Var $ "r_" ++ n +@ (show depth))] 
                  ( v' >>= (\v -> Just [eq (LReal v)  (Var $ "r_" ++ n +@ (show depth))] ))
        assrt_f    = case fee of 
          Conc r -> [eq (LReal r) (Var $ "fee_" ++ n)]
          Sym    -> (gt (LReal 1) (Var $ "fee_" ++ n)) : [gteq (Var $ "fee_" ++ n) (LReal 0) ] -- default constraints for symbolic values for the fee
          None   -> []
        stab1 = bind stab (n, DAmm)
        stab2 = bind stab1 ("l_" ++ n +@ (show depth), if null v then Symval else Concval)
        stab3 = bind stab2 ("r_" ++ n +@ (show depth), if null v' then Symval else Concval)
        stab4 = if fee /= None then bind stab3 ("fee_" ++ n, if fee == Sym then Symval else Concval) else stab3
    in Right $ (map Assert (assrt_v ++ assrt_v' ++ assrt_f), stab4)
    where 
        checkTok stab tok_name =
            let tt = get stab tok_name in
            if isJust tt && (fromJust tt == DTok) then True else False

chain :: [(String, String, String, [String])] -> [(String, String, [String])] -> Bool -> String
chain amms users useFee =
  unlines $ go amms users useFee 1 []
  where
    go _ [] _ _ acc = acc
    go [] _ _ _ acc = acc
    go ((fee, t0Amm, t1Amm, uncAmm):amms) ((t0Usr, t1Usr, uncUsr):users) useFee k acc = 
      go amms users useFee (k + 1) (acc ++ ([payout_assrtn, ite_assrtn]) ++ unc_assrtn)
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
        --posbal_assrtn = show . Assert $ gteq (Var $ prev t0Usr) (Var $ "from" +@ show k)
        unc_assrtn = 
          let uncAmms = map (\v -> show . Assert $ eq (Var $ v) (Var $ prev v)) uncAmm
              uncUsrs = map (\v -> show . Assert $ eq (Var $ v) (Var $ prev v)) uncUsr
          in uncAmms ++ uncUsrs
    prev s =
      let time = fromMaybe 1 (TR.readMaybe [(s !! (length s - 1) )] :: Maybe Int)
      in (take (length s - 1) s) ++ (show $ time - 1)
      
          
          



-- TODO: incorporate last occurrence information, when solving for green/red states
--chain :: TxSeqGuess -> [(String, String [String])] -> Int -> String
--chain guesses amms k = 
--  unlines $ (constrain_txns guesses k []) ++ (chain_assertions guesses amms 0 [])
--  where
--    constrain_txns guess k acc =
--      concat $ map (\i -> 
--            [ "(assert (> (v (from txn" ++ (show i) ++ ")) 0))"
--            , "(assert (= (user txn" ++ (show i) ++ ") \"" ++ ( fst3 $ guess!!(i-1)) ++ "\"))"
--            , "(assert (= (t (from txn" ++ (show i) ++ ")) " ++ (snd3 $ guess!!(i-1)) ++ "))"
--            , "(assert (= (t (to   txn" ++ (show i) ++ ")) " ++ (thd3 $ guess!!(i-1)) ++ "))"] ) [1..k]
--    chain_assertions guesses amms k' acc | k' == k = acc
--    chain_assertions (guess:guesses) ((n, ns, dir):nsDirs) k acc = chain_assertions guesses nsDirs (k+1) ( acc ++
--          [ "(assert (= users" ++ (show $ k + 1) ++ " (snd (swap" ++ (show dir) ++ " users" ++ (show k) ++ " txn" ++ (show $ k + 1) ++ " " ++ (n +@ (show k)) ++ "))))"
--          , "(assert (= " ++ (n +@ (show $ k + 1)) ++ " (fst (swap" ++ (show dir) ++ " users" ++ (show k) ++ " txn" ++ (show $ k + 1) ++ " " ++ (n +@ (show k)) ++ "))))"
--          , unlines $ map (\s -> "(assert (= " ++ (s +@ (show $ k + 1)) ++ " " ++ (s +@ (show k)) ++ "))") ns ])


-- TODO: make a replacement for this that basically just ensures that users with unconstrained balances are printed
--collectUsers :: Symtable -> Int -> Either String ([SMTStmt Decl Assert], Symtable)
--collectUsers stab i = 
--    let cname      = "users" ++ (show i) in
--    if isJust (get stab cname ) then Left $ " user collection already defined for depth: " ++ (show i) else
--    let users      = map fst (filter (\(k,v) -> v == DUser) (M.toList stab))
--        usersState = [Ass . Assert $  eq (Var cname) (foldl (\acc u -> store acc (Var ("\"" ++ u ++ "\"")) (Var u)) (Var "baseUsers") users)]
--        --assertions = concat $ map (\u -> [Ass . Assert $ eq (Var u) (select (Var cname) ()) ]) users
--        stab'      = bind stab (cname, DUsers)
--    in Right (usersState, stab')

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