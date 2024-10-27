{-# LANGUAGE BlockArguments #-}
module Examples.Example4 where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.Foldable
import qualified Data.Sequence as S

example4 :: TestTree
example4 =
  testCaseInfo "\n\nexample 4 \"Netting worse than standard\"\n" do
    let ex4_amms =
          [(AMM (T0, 12) (T1, 12)), 
            (AMM (T1, 18) (T2,  8))]
        ex4_txns =
          [ Swp(Swap "A" (T1, 6) (T0, 4)),
            Swp(Swap "A" (T2, 4) (T1, 6)),
            Swp(Swap "B" (T1, 6) (T0, 4)) ]
        ex4_q_len      = 2
        ex4_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 4)]) "A"
        ex4_b          = User (fromList [(AtomTok T0, 4), (AtomTok T1, 6), (AtomTok T2, 0)]) "B"
        ex4_init_state = (ex4_amms, [ex4_a, ex4_b])
        ex4_init_conf  = Configuration ex4_init_state ex4_init_state S.Empty
        (res, log)     = runTransactions False ex4_init_conf ex4_txns ex4_q_len

        expected = Configuration 
          -- green
          ([AMM (T0,  8.0) (T1, 18.0),
            AMM (T2, 12.0) (T1, 12.0) ],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A",
            User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 6.0),(AtomTok T2, 0.0)]) "B"]) 
          -- simulated
          ([AMM (T0,  8.0) (T1, 18.0),
            AMM (T2, 12.0) (T1, 12.0) ],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A",
            User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 6.0),(AtomTok T2, 0.0)]) "B"]) 
          -- queue
          (S.Empty)
        err_message = unlines (log ++ ["expected conf:"] ++ [(show expected)] ++ ["but got:"] ++ [(show res)])

    assertBool err_message (res == expected)
    return $ unlines log