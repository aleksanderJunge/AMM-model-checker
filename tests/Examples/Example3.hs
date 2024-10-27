{-# LANGUAGE BlockArguments #-}
module Examples.Example3 where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.Foldable
import qualified Data.Sequence as S

example3 :: TestTree
example3 = 
  testCaseInfo "\n\nexample 3 \"Simultaneous Exchange\"\n" do
    let ex3_amms =
          [(AMM (T0, 12) (T1, 12)), 
            (AMM (T1, 12) (T2, 12))]
        ex3_txns =
          [ Swp (Swap "B" (T1, 6) (T2, 4)),
            Swp (Swap "A" (T1, 6) (T0, 4)),
            Swp (Swap "A" (T2, 4) (T1, 6)),
            Swp (Swap "B" (T0, 4) (T1, 6)) ]
        ex3_q_len      = 3
        ex3_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 4)]) "A"
        ex3_b          = User (fromList [(AtomTok T0, 4), (AtomTok T1, 0), (AtomTok T2, 0)]) "B"
        ex3_init_state = (ex3_amms, [ex3_a, ex3_b])
        ex3_init_conf  = Configuration ex3_init_state ex3_init_state S.Empty
        (res, log)     = runTransactions False ex3_init_conf ex3_txns ex3_q_len

        expected = Configuration 
          -- green
          ([AMM (T0, 12.0) (T1, 12.0),
            AMM (T2, 12.0) (T1, 12.0) ],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A",
            User (fromList [(AtomTok T0, 0.0),(AtomTok T1, 0.0),(AtomTok T2, 4.0)]) "B"]) 
          -- simulated
          ([AMM (T0, 12.0) (T1, 12.0),
            AMM (T2, 12.0) (T1, 12.0)],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A",
            User (fromList [(AtomTok T0, 0.0),(AtomTok T1, 0.0),(AtomTok T2, 4.0)]) "B"])
          -- queue
          (S.Empty)
        err_message = unlines (log ++ ["expected conf:"] ++ [(show expected)] ++ ["but got:"] ++ [(show res)])

    assertBool err_message (res == expected)
    return $ unlines log