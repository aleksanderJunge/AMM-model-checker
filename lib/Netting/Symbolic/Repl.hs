{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Repl where

import Netting.Symbolic.Interpreter.Parser
import Netting.Symbolic.Interpreter.SymTab
import Netting.Symbolic.Sem
import Netting.Symbolic.SMT
import Data.Maybe
import Data.List
import Data.Either
import qualified Data.Map as M
import qualified GHC.Utils.Misc as Util
import qualified Text.Read as TR
import System.IO

repl :: IO ()
repl = do
  let symtab = empty :: Env String SType
  putStrLn "Declare tokens"
  (tokdecl, stab', toknames) <- toks_ symtab 
  putStrLn "Define initial state"
  (stab'', stmts, amms, users) <- init_ stab' [] [] []
  case collectUsers stab'' 0 of
    Left e -> putStrLn "you probably defined a variable called users0, it's reserved... start over"
    Right (users0, stab''') -> do
        putStrLn "initial state looks like:"
        putStrLn $ showStmts (stmts ++ users0)
        putStrLn "Set other constraints on initial state:"
        (final_stab, constraints) <- constrain stab''' (stmts ++ users0)
        putStrLn $ showStmts constraints
        putStrLn "Set constraints on final state:"
        (final_stab, final_smt) <- constrain' stab''' constraints
        putStrLn $ fromRight "error..." (buildSMTQuery (amms,users,[]) constraints final_stab 1 (tokdecl, toknames) ([("aleks", "t0", "t1")]) (EF final_smt))
  where 
    toks_ stab = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      case TR.readMaybe line :: Maybe SToks of 
        Just toks -> do
            case declToks toks stab of
                Left e -> do {putStrLn e; toks_ stab}
                Right (r, stab', toklst) -> do 
                    putStrLn r
                    if length (nub toklst) /= length toklst then do {putStrLn "duplicate token..."; toks_ stab}
                    else return (r, stab', toklst)
        Nothing -> do {putStrLn "declare tokens, e.g.: TOKENS: (t0, t1, t2)"; toks_ stab}
    init_ stab stmts amms users = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      if take 4 line == "next" then return (stab, stmts, amms, users)
      else case TR.readMaybe line :: Maybe SAMM of
        Just samm -> do
          case makeAmm samm stab of
            Left e -> do {putStrLn e; init_ stab stmts amms users}
            Right (r, stab') -> do 
                putStrLn $ showStmts r
                init_ stab' (stmts ++ r) (samm : amms) users
        Nothing ->
            case TR.readMaybe line :: Maybe SUser of 
            Just user ->
                case makeUser user stab of
                Left e -> do {putStrLn e; init_ stab stmts amms users}
                Right (r, stab') -> do 
                    putStrLn $ showStmts r 
                    init_ stab' (stmts ++ r) amms (user : users)
            Nothing -> do
                putStrLn $ "Didn't catch that"
                init_ stab stmts amms users
    constrain stab stmts = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      if take 4 line == "done" then return (stab, stmts)
      else case parse line of
            Right exp -> do 
                putStrLn "adding constraint:"
                putStrLn $ show (Assert exp)
                (constrain stab (stmts ++ [Ass . Assert $ exp]))
            Left e    -> do {putStrLn e; constrain stab stmts}
    constrain' stab stmts = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      case parse line of
        Right exp -> do 
            putStrLn "adding constraint:"
            putStrLn $ show (Assert exp)
            return (stab, exp)
        Left e    -> do {putStrLn e; constrain' stab stmts}

--instance Read Assertion where
--    readsPrec _ ('E':'F':input) =
--        case parse input of 
--            Left _ -> []
--            Right exp -> [(EF exp, "")]
--    readsPrec _ _ = []
--    --readsPrec _ ('E':input) = undefined
