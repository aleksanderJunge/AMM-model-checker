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
import System.Process ( readProcessWithExitCode )
import Control.Monad
import Control.Monad.Extra

repl :: IO ()
repl = do
  let symtab = empty :: Env String SType
  putStrLn "Declare tokens"
  (tokdecl, stab', toknames) <- toks_ symtab 
  putStrLn "Define initial state"
  (stab'', stmts, amms, users) <- init_ stab' [] [] []
  let combs =  getCombinations (amms, users) 4
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
        putStrLn "How deep to check?"
        depth <- getDepth
        satResult <- check (buildSMTQuery (amms,users,[]) constraints final_stab (tokdecl, toknames) (EF final_smt)) [1..depth] combs
        case satResult of
            Nothing -> do {putStrLn "no solution found"; repl}
            res@(Just (depth, model)) -> do
                print $ "Solution found at depth: " ++ (show depth)
                model' <- model
                putStrLn model'
                repl
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

    getDepth = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      case TR.readMaybe line :: Maybe Int of 
        Just i -> pure i
        Nothing -> do {putStrLn "Please enter an Int as depth:"; getDepth}

    init_ stab stmts amms users = do
      putStr ">> "
      hFlush stdout
      line <- getLine
      if take 4 line == "next" then return (stab, stmts, amms, users)
      else case TR.readMaybe line :: Maybe SAMM of
        Just samm -> do
          case makeAmm samm 0 stab of
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

    check buildQuery [] guesses = pure Nothing
    check buildQuery ks []      = pure Nothing 
    check buildQuery (k:ks) (guess:guesses) = do
        res <- check_at_depth buildQuery k guess
        case res of 
            Nothing  -> check buildQuery ks guesses
            Just txs -> pure $ Just (k, liftM snd txs)
    check_at_depth buildQuery k guesses = do
        txRes <- findM (\x -> liftM (not . fst) $ check_sat buildQuery k x) guesses
        case txRes of 
            Nothing -> do 
                print $ "No solution found at depth: " ++ (show k)
                pure Nothing
            -- TODO: optimize to not run sat on this twice!
            Just txs -> pure . Just $ check_sat buildQuery k txs
    check_sat buildQuery k guess = do
        putStrLn $ show guess
        writeFile "/tmp/check_goal.smt2" (case buildQuery guess k of {Left e -> error e; Right r -> r})
        (code, stdout, stderr) <- readProcessWithExitCode "z3" ["/tmp/check_goal.smt2"] ""
        case take 3 stdout of
            "sat"     -> pure (False, stdout)
            otherwise -> pure (True, stderr)