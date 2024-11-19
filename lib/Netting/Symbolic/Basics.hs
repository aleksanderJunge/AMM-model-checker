{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Basics where

import Netting.Symbolic.SymSem
import Data.Maybe
import Data.List

-- TODO: use nub for set operations!
    
makeAmm :: SAMM -> [SMTStmt Decl Assert]
makeAmm (SAMM n (v, t) (v', t')) = 
    let amm_name = singleton . Dec $ DeclVar n TAmm 
        name_t   = concat . maybeToList $ t  >>= decl_t getr0
        name_t'  = concat . maybeToList $ t' >>= decl_t getr1
        name_v   = concat . maybeToList $ v  >>= decl_v getr0
        name_v'  = concat . maybeToList $ v' >>= decl_v getr1
    in amm_name ++ name_t ++ name_t' ++ name_v ++ name_v'
    where 
        decl_t get_r name = return [Dec $ DeclVar name TToken, Ass . Assert $ eq (Var name) (gett . get_r $ Var n)]
        decl_v get_r name = return [Dec $ DeclVar name TReal,  Ass . Assert $ eq (Var name) (getv . get_r $ Var n)]
        
showStmts :: [SMTStmt Decl Assert] -> String
showStmts stmts = 
    let (decs, asses) = partition (\case {Dec _ -> True; Ass _ -> False}) stmts in
    unlines $ map showStmt (decs ++ asses)
    where 
        showStmt =
            \case
                Dec decl -> show decl
                Ass ass  -> show ass