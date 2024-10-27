{-# LANGUAGE BlockArguments #-}
module Examples.Example6 where

import Test.Tasty
import Test.Tasty.HUnit
import Netting.Sem
import Netting.AmmFuns

import Data.Map
import Data.List
import Data.Foldable
import qualified Data.Sequence as S

example6 :: TestTree
example6 =
  testCaseInfo "\n\nexample 6 \"Netting Maximum Overdraft\"\n" do
    let ex6_amms =
            [(AMM (T0, 12) (T1, 12)), 
             (AMM (T1, 18) (T2,  8)),
             (AMM (T2, 12) (T0, 12)) ]
        ex6_txns =
            [ Swp( Swap "A" (T2, 6) (T0, 4)),
              Swp( Swap "A" (T1, 6) (T0, 4)),
              Swp( Swap "A" (T2, 4) (T1, 6)),
              Swp( Swap "A" (T0, 3) (T2, 4)),
              Swp( Swap "A" (T0, 4) (T1, 6))]
        ex6_q_len      = 4
        ex6_a          = User (fromList [(AtomTok T0, 0), (AtomTok T1, 0), (AtomTok T2, 4)]) "A"
        ex6_init_state = (ex6_amms, [ex6_a])
        ex6_init_conf  = Configuration ex6_init_state ex6_init_state S.Empty
        (res, log)     = runTransactions True ex6_init_conf ex6_txns ex6_q_len

        expected = Configuration 
            -- green
            ([AMM (T0, 12.0) (T1, 12.0),
              AMM (T1, 18.0) (T2,  8.0),
              AMM (T2, 144 / 11) (T0, 11.0) ],
            [User (fromList [(AtomTok T0, 1),(AtomTok T1, 0),(AtomTok T2, 32 / 11)]) "A"])
            -- simulated
            ([AMM (T0, 12.0) (T1, 12.0),
              AMM (T1, 18.0) (T2,  8.0),
              AMM (T2, 144 / 11) (T0, 11.0) ],
            [User (fromList [(AtomTok T0, 1),(AtomTok T1, 0),(AtomTok T2, 32 / 11)]) "A"])
            -- queue
            (S.Empty)
        err_message = unlines (log ++ ["expected conf:"] ++ [(show expected)] ++ ["but got:"] ++ [(show res)])

    assertBool err_message (res == expected)
    return $ unlines log