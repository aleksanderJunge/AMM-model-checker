module Main where

import Control.Monad
import Data.Map
import Data.Maybe
import Netting.Sem
import Netting.AmmFuns
--import qualified Data.Sequence as S
--import Netting.Symbolic.SMT_opt
import Netting.Symbolic.Basics
import Netting.Symbolic.SymSem

import System.IO


main :: IO ()
main = do
  let samm = SAMM "t0t1_0" (Just "t", Nothing) (Nothing, Nothing)
      smtrepresentation = makeAmm samm
  putStrLn $ showStmts smtrepresentation
  repl
  return ()
  where 
    repl = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      let justRead = words line
      if elem "bye" justRead then return ()
      else do
        let toParse = concat justRead
            samm = read toParse :: SAMM
            smts = showStmts $ makeAmm samm
        putStrLn $ smts
        repl
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