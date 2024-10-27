module Netting.Sim where

-- A simulation library for generating transactions and executions

import Netting.Sem
import Netting.AmmFuns
import Netting.Worth
import System.Random
import Data.List
import Data.Maybe

-- generate a random float in range [from, to]
--genInRange :: (Float, Float) -> IO Float
--genInRange (from, to) = getStdRandom (randomR (from, to))
--  
---- constructs the single highest gain transaction for the user 'name' in state s (not caring if he can afford to execute it)
--genSingleArbitrageTxn :: String -> State -> Swap
--genSingleArbitrageTxn name s@(amms, users) =
--  let input_output_pairs = map singleAmmArbitrage amms
--      transactions       = map (\(x, y) -> Swap name x y) input_output_pairs
--      gains              = map (flip txnGain s) transactions
--  in 
--      transactions !! fromMaybe 0 (elemIndex (maximum gains) gains)
--
---- TODO: Add more functions to generate transactions