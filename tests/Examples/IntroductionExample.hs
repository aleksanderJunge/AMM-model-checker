{-# LANGUAGE BlockArguments #-}
module Examples.IntroductionExample where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.Foldable
import qualified Data.Sequence as S

introductionExample :: TestTree
introductionExample = 
  testCaseInfo "\n\nIntroduction Example; Interaction between three users and two AMMs\n" do
    let amms =
          [(AMM (T1, 12) (T2, 12))]
        txns =
          [ Dep (Deposit "C" (T0, 12) (T1, 12)),
            Swp (Swap    "B" (T1,  6) (T2,  4)),
            Swp (Swap    "A" (T1,  6) (T0,  4)),
            Swp (Swap    "A" (T2,  4) (T1,  6)),
            Swp (Swap    "B" (T0,  4) (T1,  6)),
            Rdm (Redeem  "C" (MT (T0,T1), 6))]
        q_len      = 3
        a          = User (fromList [(AtomTok T0,  0), (AtomTok T1,  0), (AtomTok T2, 4)]) "A"
        b          = User (fromList [(AtomTok T0,  4), (AtomTok T1,  0), (AtomTok T2, 0)]) "B"
        c          = User (fromList [(AtomTok T0, 12), (AtomTok T1, 14), (AtomTok T2, 0)]) "C"
        init_state = (amms, [a, b, c])
        init_conf  = Configuration init_state init_state S.Empty
        (res, log) = runTransactions False init_conf txns q_len

        expected = Configuration 
          -- green
          ([AMM (T2, 12.0) (T1, 12.0),
            AMM (T0,  6.0) (T1,  6.0)],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A",
            User (fromList [(AtomTok T0, 0.0),(AtomTok T1, 0.0),(AtomTok T2, 4.0)]) "B",
            User (fromList [(AtomTok T0, 6.0),(AtomTok T1, 8.0),(AtomTok T2, 0.0), (MintTok $ MT (T0, T1), 6.0)]) "C"]) 
          -- simulated
          ([AMM (T2, 12.0) (T1, 12.0),
            AMM (T0,  6.0) (T1,  6.0)],
            [User (fromList [(AtomTok T0, 4.0),(AtomTok T1, 0.0),(AtomTok T2, 0.0)]) "A",
            User (fromList [(AtomTok T0, 0.0),(AtomTok T1, 0.0),(AtomTok T2, 4.0)]) "B",
            User (fromList [(AtomTok T0, 6.0),(AtomTok T1, 8.0),(AtomTok T2, 0.0), (MintTok $ MT (T0, T1), 6.0)]) "C"]) 
          -- queue
          (S.Empty)
        err_message = unlines (log ++ ["expected conf:"] ++ [(show expected)] ++ ["but got:"] ++ [(show res)])

    assertBool err_message (res == expected)
    return $ unlines log
