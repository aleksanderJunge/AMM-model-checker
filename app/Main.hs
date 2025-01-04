{-# LANGUAGE LambdaCase #-}

module Main where

import Symbolic.Repl

main :: IO ()
main = do
  out <- repl
  case out of
    Left err -> do {putStrLn err; return ()}
    _ -> return ()
  