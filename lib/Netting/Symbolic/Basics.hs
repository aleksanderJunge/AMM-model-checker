{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Basics where

import Netting.SymTab
import Netting.Symbolic.SymSem
import Data.Maybe
import Data.List
import Data.Either
import qualified Data.Map as M

import qualified GHC.Utils.Misc as Util

-- TODO: use nub for set operations!

    
-- TODO: enable parsing more numbers and check for subzero
makeAmm :: SAMM -> Env String SType -> Either String ([SMTStmt Decl Assert], Env String SType)
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

makeUser :: SUser -> Env String SType -> Either String ([SMTStmt Decl Assert], Env String SType)
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
declToks :: SToks -> Env String SType -> Either String (String, Env String SType)
declToks (SToks toks) stab =
    if elem DTok (codomain stab) then Left "Tokens have already been declared!" else
        let stab' = foldl (\st tok -> bind st (tok, DTok)) stab toks in
    Right ("(declare-datatype Token ("++ (concat $ intersperse " " $ map (\x -> '(':x ++ ")") toks) ++ "))", stab')
        
showStmts :: [SMTStmt Decl Assert] -> String
showStmts stmts = 
    let (decs, asses) = partition (\case {Dec _ -> True; Ass _ -> False}) stmts in
    unlines $ map showStmt (decs ++ asses)
    where 
        showStmt =
            \case
                Dec decl -> show decl
                Ass ass  -> show ass