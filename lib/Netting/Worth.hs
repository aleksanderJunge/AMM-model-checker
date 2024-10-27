module Netting.Worth where

import Netting.Sem
import Netting.AmmFuns
import qualified Data.Map as M
import Data.Either


-- can be used to provision AMMs and txns with "real" exchange rates
-- it assumes t0 ~= BTC, t1 ~= ETH, and T2 ~= USD
oracleXRate :: AtomicToken -> AtomicToken -> Float
oracleXRate T0 T0 = 1.0
oracleXRate T0 T1 = 22.70
oracleXRate T0 T2 = 58793.6

oracleXRate T1 T1 = 1.0 
oracleXRate T1 T0 = 1.0 / oracleXRate T0 T1
oracleXRate T1 T2 = 2596.76

oracleXRate T2 T2 = 1.0
oracleXRate T2 T0 = 1.0 / oracleXRate T0 T2
oracleXRate T2 T1 = 1.0 / oracleXRate T1 T2


-- netWorth denoted in T2, calculated using the oracle exchange rate
--netWorth :: User -> Float
--netWorth (User wallet _) = 
--    M.foldrWithKey (\k v acc -> acc + v * (oracleXRate k T2)) 0 wallet
--
--
---- calcualtes the gain made by 'name' as his net worth in s' minus net worth in s
--gain :: String -> State -> State -> Maybe Float
--gain name (_, users) (_, users') =
--    case findUserIdx users name of
--        Nothing  -> Nothing -- if user not in s, return Nothing
--        Just idx -> 
--            case findUserIdx users' name of 
--                Nothing -> Nothing
--                Just idx' -> Just $ netWorth (users' !! idx') - netWorth (users !! idx)
--
--
---- calcualtes the gain made by 'name' after transaction txn in s
--txnGain :: Swap -> State -> Maybe Float
--txnGain txn@(Swap name _ _) s@(_, users) =
--  case findUserIdx users name of
--    Nothing  -> Nothing -- if user not in s, return Nothing
--    Just idx -> 
--      let worth              = netWorth (users !! idx)
--          s'@(amms', users') = fromRight s (executeSwap s txn)
--          worth'             = netWorth (users' !! idx) -- fine, as executeSwap shouldn't reorder users
--      in
--          Just $ worth' - worth
--
--
---- considers the arbitrage game on a single CFMM AMM (https://lmcs.episciences.org/10504/pdf, lemma 6.4)
---- returns the 'input swap amount' that brings AMM back into equilibrium with oracle rate
--singleAmmArbitrage :: AMM -> (TokenAmt, TokenAmt)
--singleAmmArbitrage amm@(AMM (t0, r0) (t1, r1)) =
--  if r1 / r0 > oracleXRate t0 t1 then 
--    -- t1 is cheap compared to oracle rate, thus swap(t0, t1) gives pos gain
--    let v0 = sqrt (oracleXRate t1 T2 / oracleXRate t0 T2 * r0 * r1) - r0 in 
--        ((t0, v0), payout amm (t0, v0))
--  else 
--    -- t0 is cheap compared to oracle rate, thus swap(t1, t0) gives pos gain
--    let v1 = sqrt (oracleXRate t0 T2 / oracleXRate t1 T2 * r1 * r0) - r1 in 
--        ((t1, v1), payout amm (t1, v1))
--  where 
--    payout (AMM (t0, r0) (t1, r1)) (t2, v0) -- payout that preserves CFMM properties
--      | t0 == t2  = (t1, (r1 * v0) / (r0 + v0)) 
--      | otherwise = (t0, (r0 * v0) / (r1 + v0))
--          