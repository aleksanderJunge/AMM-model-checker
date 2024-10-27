{-# LANGUAGE BlockArguments #-}
module OtherTests.RateAttack where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.Foldable
import qualified Data.Sequence as S

rateAttack :: TestTree
rateAttack = 
  testCaseInfo "\nrateAttack; What a malicious user could do" do
    let amms = 
          [(AMM (T0, 1e6) (T1, 1e6))]

        txns = 
          [ Swp (Swap "M" (T0, 1e20) (T1, 0)),
            Swp (Swap "M" (T1, 1e4)  (T0, 0)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "A" (T0, 1e3) (T1, 1e3 - 3)),
            Swp (Swap "B" (T1, 1e3) (T0, 1e3 - 3)),
            Swp (Swap "C" (T1, 1e3) (T0, 1e3 - 3))]

        q_len      = 11
        a          = User (fromList [(AtomTok T0, 1e4), (AtomTok T1, 1e4)]) "A"
        b          = User (fromList [(AtomTok T0, 1e4), (AtomTok T1, 1e4)]) "B"
        c          = User (fromList [(AtomTok T0, 1e4), (AtomTok T1, 1e4)]) "C"
        m          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 0)]) "M"
        init_state = (amms, [a,b,c,m])
        init_conf  = Configuration init_state init_state S.Empty
        (res, log)     = runTransactions False init_conf txns q_len

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