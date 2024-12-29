{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad
--import Data.Map
import Data.Maybe
import Netting.Sem
import Netting.AmmFuns
--import qualified Data.Sequence as S
--import Netting.Symbolic.SMT_opt
import Netting.Symbolic.Repl
import Netting.Symbolic.Sem
--import Netting.Interpreter.SymTab
import Netting.Symbolic.Interpreter.Parser
--import Data.List.Split
--import Data.List
--import qualified GHC.Utils.Misc as Util
--import Data.Either
--import Data.Either.Extra
--import Data.Char
--import Text.Read hiding (prec)

main :: IO ()
main = do
  repl 
  return ()