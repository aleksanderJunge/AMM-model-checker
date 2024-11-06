
{-# LANGUAGE BlockArguments #-}
module Examples.Example1 where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.Foldable
import qualified Data.Sequence as S

example1 :: TestTree
example1 = 
  testCaseInfo "\n\nexample 1 \"Negative Balance Covered\"\n" do
    let ex1_amms = 
          [(AMM (T0, 8) (T1, 18)),
            (AMM (T1, 8) (T2, 18)),
            (AMM (T2, 8) (T0, 18)) ]

        --ex1_txns = 
        --  [ Swp (Swap "A" (T2, 4.0) (T0, 0)),
        --    Swp (Swap "A" (T0, 4.0) (T1, 0)),
        --    Swp (Swap "A" (T1, 4.0) (T2, 0)) ]
        ex1_txns = 
          [ Swp (Swap "A" (T0, 2.5) (T1, 1)),
            Swp (Swap "A" (T1, 40/13) (T2, 1.0)),
            Swp (Swap "A" (T2, 2.0) (T0, 1)) ]

        ex1_q_len      = 2
        ex1_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 0)]) "A"
        ex1_init_state = (ex1_amms, [ex1_a])
        ex1_init_conf  = Configuration ex1_init_state ex1_init_state S.Empty
        (res, log)     = runTransactions False ex1_init_conf ex1_txns ex1_q_len

        expected = Configuration 
          -- green
          ([AMM (T0, 12.0) (T1, 12.0),
            AMM (T1, 12.0) (T2, 12.0),
            AMM (T2, 12.0) (T0, 12.0) ],
            [User (fromList [(AtomTok T0, 2.0),(AtomTok T1, 2.0),(AtomTok T2, 2.0)]) "A"])
          -- simulated
          ([AMM (T0, 12.0) (T1, 12.0),
            AMM (T1, 12.0) (T2, 12.0),
            AMM (T2, 12.0) (T0, 12.0) ],
            [User (fromList [(AtomTok T0, 2.0),(AtomTok T1, 2.0),(AtomTok T2, 2.0)]) "A"])
          -- queue
          (S.Empty)
        err_message = unlines (log ++ ["expected conf:"] ++ [(show expected)] ++ ["but got:"] ++ [(show res)])

    assertBool err_message (res == expected)
    return $ unlines log