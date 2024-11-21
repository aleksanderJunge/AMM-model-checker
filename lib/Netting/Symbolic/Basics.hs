{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Basics where

import Netting.Symbolic.SymSem
import Data.Maybe
import Data.List

-- TODO: use nub for set operations!

    
-- TODO: enable parsing more numbers and check for subzero
makeAmm :: SAMM -> [SMTStmt Decl Assert]
makeAmm (SAMM n (v, t) (v', t')) =
    let amm_name = singleton . Dec $ DeclVar n TAmm 
        val_v    = fromMaybe [] ( v  >>= (\v -> Just [Ass . Assert $ eq (LReal v)  (getv . getr0 $ Var n)] ))
        val_v'   = fromMaybe [] ( v' >>= (\v -> Just [Ass . Assert $ eq (LReal v)  (getv . getr1 $ Var n)] ))
        val_t    = fromMaybe [] ( t  >>= (\t -> Just [Ass . Assert $ eq (LTok  t)  (gett . getr0 $ Var n)] ))
        val_t'   = fromMaybe [] ( t' >>= (\t -> Just [Ass . Assert $ eq (LTok  t)  (gett . getr1 $ Var n)] ))
        distinctness = [Ass . Assert $ distinct (gett . getr0 $ Var n) (gett . getr1 $ Var n)]
        pos_v   = if null val_v  then [Ass . Assert $ lt (LReal 0) (getv . getr0 $ Var n)] else []
        pos_v'  = if null val_v' then [Ass . Assert $ lt (LReal 0) (getv . getr1 $ Var n)] else []
    in amm_name ++ val_v ++ val_v' ++ val_t ++ val_t' ++ distinctness ++ pos_v ++ pos_v'


--makeAmm :: SAMM -> [SMTStmt Decl Assert]
--makeAmm (SAMM n (v, t) (v', t')) = 
--    let amm_name = singleton . Dec $ DeclVar n TAmm 
--        name_t   = concat . maybeToList $ t  >>= decl_t getr0
--        name_t'  = concat . maybeToList $ t' >>= decl_t getr1
--        name_v   = concat . maybeToList $ v  >>= decl_v getr0
--        name_v'  = concat . maybeToList $ v' >>= decl_v getr1
--    in amm_name ++ name_t ++ name_t' ++ name_v ++ name_v'
--    where 
--        decl_t get_r name = return [Dec $ DeclVar name TToken, Ass . Assert $ eq (Var name) (gett . get_r $ Var n)]
--        decl_v get_r name = return [Dec $ DeclVar name TReal,  Ass . Assert $ eq (Var name) (getv . get_r $ Var n)]


-- given a list of names, declares these to be the set of tokens
declToks :: SToks -> String
declToks (SToks toks) = "(declare-datatype Token "++ (concat $ intersperse " " $ map (\x -> '(':x ++ ")") toks) ++ "))"
        
showStmts :: [SMTStmt Decl Assert] -> String
showStmts stmts = 
    let (decs, asses) = partition (\case {Dec _ -> True; Ass _ -> False}) stmts in
    unlines $ map showStmt (decs ++ asses)
    where 
        showStmt =
            \case
                Dec decl -> show decl
                Ass ass  -> show ass