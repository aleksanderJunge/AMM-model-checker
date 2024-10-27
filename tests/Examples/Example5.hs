{-# LANGUAGE BlockArguments #-}
module Examples.Example5 where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.Foldable
import qualified Data.Sequence as S

example5 :: TestTree
example5 =
  testCaseInfo "\n\nexample 5 \"Netting scenario\"\n" do
    let ex5_amms =
          [(AMM (T0, 12) (T1, 12)), 
            (AMM (T1, 18) (T2,  8)),
            (AMM (T2, 12) (T0, 12))]
        ex5_txns =
          [ Swp (Swap "A" (T2, 6) (T0, 4)),
            Swp (Swap "A" (T1, 6) (T0, 4)),
            Swp (Swap "A" (T2, 4) (T1, 6)) ]
        ex5_q_len      = 2
        ex5_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 4)]) "A"
        ex5_init_state = (ex5_amms, [ex5_a])
        ex5_init_conf  = Configuration ex5_init_state ex5_init_state S.Empty
        (res, log)     = runTransactions False ex5_init_conf ex5_txns ex5_q_len

        expected = Configuration 
          -- green
          ([AMM (T0,  8.0) (T1, 18.0),
            AMM (T1, 12.0) (T2, 12.0),
            AMM (T2, 12.0) (T0, 12.0)],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A"])
          -- simulated
          ([AMM (T0,  8.0) (T1, 18.0),
            AMM (T1, 12.0) (T2, 12.0),
            AMM (T2, 12.0) (T0, 12.0)],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A"])
          -- queue
          (S.Empty)
        err_message = unlines (log ++ ["expected conf:"] ++ [(show expected)] ++ ["but got:"] ++ [(show res)])

    assertBool err_message (res == expected)
    return $ unlines log