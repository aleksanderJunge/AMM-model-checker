{-# LANGUAGE BlockArguments #-}
module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Examples.IntroductionExample
import Examples.Example1
import Examples.Example2
import Examples.Example3
import Examples.Example4
import Examples.Example5
import Examples.Example6
import OtherTests.RateAttack


tests :: TestTree
tests = sequentialTestGroup "Paper Examples" AllFinish 
  [introductionExample,
   example1,
   example2,
   example3,
   example4,
   example5,
   example6,
   rateAttack]

main :: IO ()
main = defaultMain tests 