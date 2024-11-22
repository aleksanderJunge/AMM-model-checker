{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Basics where

import Netting.SymTab
import Netting.Symbolic.SymSem
import Data.Maybe
import Data.List
import Data.Either

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