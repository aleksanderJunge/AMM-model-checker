{-# LANGUAGE LambdaCase #-}

module Main where

import Symbolic.Repl

main :: IO ()
main = do
  repl 
  return ()