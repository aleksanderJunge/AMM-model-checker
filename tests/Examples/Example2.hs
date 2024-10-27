{-# LANGUAGE BlockArguments #-}
module Examples.Example2 where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.Foldable
import qualified Data.Sequence as S

example2 :: TestTree
example2 = 
  testCaseInfo "\n\nexample 2 \"r-swap and AMM creation\"\n" do
    let ex2_amms = 
          [(AMM (T0, 8) (T1, 18))]

        ex2_txns = 
          [ Swp (Swap    "A" (T0, 4) (T1, 6)),
            Dep (Deposit "A" (T1, 6) (T2, 6)),
            Swp (Swap    "B" (T1, 6) (T2, 3))]

        ex2_q_len      = 2
        ex2_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 6)]) "A"
        ex2_b          = User (fromList [(AtomTok T0, 6), (AtomTok T1, 6), (AtomTok T2, 0)]) "B"
        ex2_init_state = (ex2_amms, [ex2_a, ex2_b])
        ex2_init_conf  = Configuration ex2_init_state ex2_init_state S.Empty
        (res, log)     = runTransactions False ex2_init_conf ex2_txns ex2_q_len

        expected = Configuration 
          -- green
          ([AMM (T0, 8.0) (T1, 18.0)],
            [User (fromList [(AtomTok T0, 0.0),(AtomTok T1, 0.0),(AtomTok T2, 6.0)]) "A",
             User (fromList [(AtomTok T0, 6.0),(AtomTok T1, 6.0),(AtomTok T2, 0.0)]) "B"])
          -- simulated
          ([AMM (T0, 8.0) (T1, 18.0)],
            [User (fromList [(AtomTok T0, 0.0),(AtomTok T1, 0.0),(AtomTok T2, 6.0)]) "A",
             User (fromList [(AtomTok T0, 6.0),(AtomTok T1, 6.0),(AtomTok T2, 0.0)]) "B"])
          -- queue
          (S.Empty)
        err_message = unlines (log ++ ["expected conf:"] ++ [(show expected)] ++ ["but got:"] ++ [(show res)])

    assertBool err_message (res == expected)
    return $ unlines log
