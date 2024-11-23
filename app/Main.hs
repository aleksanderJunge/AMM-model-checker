module Main where

import Control.Monad
--import Data.Map
import Data.Maybe
import Netting.Sem
import Netting.AmmFuns
--import qualified Data.Sequence as S
--import Netting.Symbolic.SMT_opt
import Netting.Symbolic.Basics
import Netting.Symbolic.SymSem
import Netting.SymTab
import Text.Read

import System.IO

main :: IO ()
main = do
  let symtab = empty :: Env String SType
  repl symtab
  return ()
  where 
    repl stab = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      case readMaybe line :: Maybe SAMM of
        Just samm -> do
          case makeAmm samm stab of
            Left e -> do {putStrLn e; repl stab}
            Right (r, stab') -> do {putStrLn $ showStmts r; repl stab'}
        Nothing ->
          case readMaybe line :: Maybe SToks of 
            Just toks -> do
              case declToks toks stab of
                Left e -> do {putStrLn e; repl stab}
                Right (r, stab') -> do {putStrLn r; repl stab'}
            Nothing -> do
              case readMaybe line :: Maybe SUser of 
                Just user ->
                  case makeUser user stab of
                    Left e -> do {putStrLn e; repl stab}
                    Right (r, stab') -> do {putStrLn $ showStmts r; repl stab'}
                Nothing -> do
                  putStrLn $ "Didn't catch that: " ++ line
                  repl stab
    --let ex1_amms = 
    --      [(AMM (T0, 8) (T1, 18)),
    --       (AMM (T1, 8) (T2, 18)),
    --       (AMM (T2, 8) (T0, 18)) ]

    --    ex1_q_len      = 2
    --    ex1_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 0)]) "A"
    --    ex1_init_state = (ex1_amms, [ex1_a])
    --    ex1_init_conf  = Configuration ex1_init_state ex1_init_state S.Empty
    --    ex5_amms =
    --      [(AMM (T0, 12) (T1, 12)), 
    --        (AMM (T1, 18) (T2,  8)),
    --        (AMM (T2, 12) (T0, 12))]
    --    ex5_q_len      = 2
    --    ex5_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 6)]) "A"
    --    ex5_a'         = User (fromList [(AtomTok T0, 4), (AtomTok T1, 0), (AtomTok T2, 0)]) "A"
    --    ex5_init_state = (ex5_amms, [ex5_a])
    --    ex5_init_conf  = Configuration ex5_init_state ex5_init_state S.Empty
    --    ex3_amms =
    --      [(AMM (T0, 12) (T1, 12)), 
    --        (AMM (T1, 12) (T2, 12))]
    --    ex3_q_len      = 3
    --    ex3_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 4)]) "A"
    --    ex3_b          = User (fromList [(AtomTok T0, 4), (AtomTok T1, 0), (AtomTok T2, 0)]) "B"
    --    ex3_init_state = (ex3_amms, [ex3_a, ex3_b])
    --    ex3_init_conf  = Configuration ex3_init_state ex3_init_state S.Empty       

    ----res' <- checkGoal ex1_init_conf 3 [(U ("A", [(T0, 2), (T1, 2), (T2, 2)])) ]
    ----res' <- checkGoal ex1_init_conf 3 [(U ("A", [(T0, 2), (T1, 2), (T2, 2)])) ]
    --res  <- checkGoal ex3_init_conf 4 [(U ("A", [(T0, 4)])), (U ("B", [(T2, 4)]))]
    --return ()