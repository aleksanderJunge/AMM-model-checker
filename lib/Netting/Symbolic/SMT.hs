{-# LANGUAGE LambdaCase #-}
module Netting.Symbolic.SMT where

import Netting.Sem
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe
import Data.Ratio (denominator, numerator)

data Goal = U (String, [TokenAmt]) -- S State

-- build query to check if goal is reachable within exactly k steps
buildSMTQuery :: Configuration -> Int -> Goal -> String
buildSMTQuery (Configuration g s q) k goal =
    case goal of
        U (n, amts) -> 
            baseAxioms
            ++ buildVars k
            ++ constrainState s 0 -- (assuming s = g)
            ++ constrainTxns (snd g) k
            ++ (unlines $ map buildChainAssertions [k])
            ++ userGoal amts n k
            ++ sat k (map name (snd s))
            ++ (unlines $ map (\i -> "(get-value (txn" ++ i ++ "))") $ map show [0..k-1])
    where sat k ns = unlines
            [ "(assert (forall ((tau Token))"
            , "(and" ]
            ++ unlines (map (\n -> "(>= (getBal state" ++ (show k) ++ " \"" ++ n ++ "\" tau) 0)") ns)
            ++ ")))"
            ++ "(check-sat)"

-- a desired basket of tokens
userGoal :: [TokenAmt] -> String -> Int -> String
userGoal ts n k = unlines $
    map (\(t,v) -> 
        "(assert (= "++ (showR v) ++ " (select (select (users state" 
        ++ (show k) ++ ") \"" ++ n ++ "\") " ++ (show t) ++ ")))") ts

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

-- given a list of eligible transaction senders, constrains txns
constrainTxns :: [ User ] -> Int -> String
constrainTxns us k =
    let ns = map name us
        ks = [0..k-1] in
        unlines $ (assertSender ns ks) ++ (assertAmount ks) ++ (assertDistinct ks)
    where 
        assertSender ns ks = map (\k -> unlines $
            [ "(assert (xor"
            , unlines $ map (\n -> "  (= (user txn" ++ (show k) ++ ") \"" ++ n ++ "\")") ns
            , "))"]) ks
        assertAmount ks = map (\i -> "(assert (> (v (from txn" ++ (show i) ++ ")) 0 ))") ks
        assertDistinct ks = map (\i -> "(assert (distinct (t (from txn" ++ (show i) ++ ")) (t (to txn" ++ (show i) ++ "))))" ) ks
            
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
          build_assertions 0 s = ammAssertions ++ s
          build_assertions i s = build_assertions (i - 1) 
            (unlines 
                [ "(assert (= state" ++ (show i) ++ " (swap state" ++ (show $ i - 1) ++ " txn" ++ (show $ i - 1) ++ ")))"] : s)
          ammAssertions = 
            [ "(assert (forall ((tau1 Token) (tau2 Token))"
            , "(and "
            , "    (= (select (select (amms state0) tau1) tau2) "
            , "       (select (select (amms state0) tau2) tau1))"
            , "    (match (select (select (amms state0) tau1) tau2) ((nothing true)" 
            , "    ((just a) (distinct (t (r0 a)) (t (r1 a))))))"
            , "    (match (select (select (amms state0) tau1) tau2) ((nothing true)" 
            , "    ((just a) (and (< 0 (v (r0 a))) (< 0 (v (r1 a)))))))"
            , "    (match (select (select (amms state0) tau1) tau2) ((nothing true)"  
            , "    ((just a)  "
            , "        (xor (and (= (t (r0 a)) tau1) (= (t (r1 a)) tau2)) "
            , "             (and (= (t (r1 a)) tau1) (= (t (r0 a)) tau2)))))))))"]


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
  , "( declare-datatypes (( Maybe 1 )) ("
  , "( par ( X ) ( ( nothing ) ( just ( val X ))))))"
  , ""
  , "( declare-datatype State ("
  , "    (pair (amms  (Array Token (Array Token (Maybe Amm))))"
  , "          (users (Array String (Array Token Real)))"
  , "    )"
  , "))"
  , ""
  , "( declare-datatype Txn (( tx ( user String ) ( from TokenAmount ) ( to TokenAmount))))"
  , ""
  , "( define-fun swap ((state State)"
  , "                   (swp   Txn))"
  , "                   State"
  , "("
  , "     ite (> 0 (v (from swp))) state"
  , "    (let ((foundAmm (select (select (amms state) (t (from swp))) (t (to swp)))))"
  , "        ( match foundAmm ((nothing state) ((just foundAmmX)"
  , "        (let ((swappingAmm ("
  , "            ite (= (t (r0 foundAmmX)) (t (from swp)))"
  , "                   foundAmmX"
  , "                   (amm (r1 foundAmmX) (r0 foundAmmX)))))"
  , "        ; Calculate payout"
  , "        (let ((payout (/ (* (v (from swp)) (v (r1 swappingAmm)))"
  , "                         (+ (v (from swp)) (v (r0 swappingAmm))))))"
  , "              ; If swap withing x-rate, then execute, otherwise leave state unchanged"
  , "             (ite (and (<= 0      (v (to swp)))"
  , "                       (<= (v (to swp)) payout))"
  , "                  (let ((oldBal (select (users state) (user swp))))"
  , "                    ("
  , "                    let ((newBal"
  , "                            (store"
  , "                                (store oldBal"
  , "                                       (t (to swp))"
  , "                                       (+ (select oldBal (t (to swp))) payout)"
  , "                                )"
  , "                                (t (from swp)) "
  , "                                (- (select oldBal (t (from swp)))"
  , "                                   (v (from swp)))))"
  , "                         (newAmm (amm"
  , "                                  (amount (t (from swp)) (+ (v (r0 swappingAmm)) (v (from swp))))"
  , "                                  (amount (t (to swp)  ) (- (v (r1 swappingAmm)) payout))"
  , "                                  ))"
  , "                         )"
  , "                    ; return new state"
  , "                    (pair"
  , "                        (let ((oldTFromAmms (select (amms state) (t (from swp))))"
  , "                              (oldTToAmms   (select (amms state) (t (to swp)  ))))"
  , "                              ; update lookup corresponding to selecting t0 -> t1"
  , "                             (let ((tmpamms (store (amms state ) (t (from swp))"
  , "                                (store oldTFromAmms (t (to swp)) (just newAmm)))))"
  , "                              (store tmpamms (t (to swp)) (store oldTToAmms (t (from swp)) (just newAmm)))))"
  , "                        (store (users state) (user swp) newBal)"
  , "                        )))"
  , "                  state"
  , "            )"
  , "    )"
  , ")))))))"
  , "( define-fun getBal ((state State)"
  , "                     (name String)"
  , "                     (tau  Token)) "
  , "                      Real "
  , "("
  , "    select (select (users state) name) tau"
  , "))"
  , "(define-fun lempt () (Array Token (Maybe Amm))"
  , "((as const (Array Token (Maybe Amm))) nothing))"
  , "(define-fun hempt () (Array Token (Array Token (Maybe Amm)))"
  , "((as const (Array Token (Array Token (Maybe Amm)))) lempt))" 
  , "(define-fun baseUsers () (Array String (Array Token Real))"
  , "((as const (Array String (Array Token Real)))"
  , "         ((as const (Array Token Real)) 0.0)))"
  , "(define-fun baseWal () (Array Token Real)"
  , "((as const (Array Token Real)) 0.0))"
  ]
