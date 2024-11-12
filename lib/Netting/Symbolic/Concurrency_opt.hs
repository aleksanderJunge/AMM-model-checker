{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Concurrency_opt where

import System.Process
import System.IO.Error
import GHC.IO.Handle
import Control.Concurrent
import Data.List
import Data.Maybe
import Data.Tuple.Extra
import Control.Monad
import Control.Monad.Extra
--import System.Directory

waitForJob :: [(Handle, Handle, ProcessHandle, Int)] -> IO Int
waitForJob ps = do
    done <- findM (\(hi, ho, ph, i) -> hWaitForInput ho 1) ps
    case done of
        Nothing -> do 
            threadDelay 2500 -- TODO: Figure out opt waiting time
            waitForJob ps --termination not guaranteed, wonderful :D
        Just (_, _, _, i)  -> do 
            pure i

-- give SMT job to worker through pipe
enqueueJob :: [(Handle, Handle, ProcessHandle, Int)] -> Int -> String -> IO ()
enqueueJob ps i query = do
    let (hin, _, _, _) = ps !! i -- safe as call site has i < length ps
    hPutStr hin query
    hFlush hin

script :: String
script = unlines $ [
    "#! /usr/bin/bash"
  , "while read -d '~' input; do"
  , "echo \"$input\" | z3 -in"
  --, "echo \"$input\" > ./smtwork$$.smt2"
  --, "z3 ./smtwork$$.smt2"
  , "done"]
  --, "rm ./smtwork$$.smt2"]

createWorkers :: Int -> IO [(Handle, Handle, ProcessHandle, Int)]
createWorkers n = do
    let filename = "/tmp/worker.sh"
        indices  = [0..n-1]
    writeFile filename script
    --perms <- getPermissions "/tmp/worker.sh"
    --setPermissions "/tmp/worker.sh" perms {executable=True}
    workers <- replicateM n (createProc filename) -- is writeFile blocking until completion? otherwise might fail
    pure $ map (\((hin, hout, phdl), i) -> (hin, hout, phdl, i)) (zip workers indices)
    where createProc filename = do
            (Just hin, Just hout, _, pHdl) <- 
              createProcess (proc "bash" [filename]){std_in  = CreatePipe, 
                                                     std_out = CreatePipe}
            pure (hin, hout, pHdl)

initWorkers :: [(Handle, Handle, ProcessHandle, Int)] -> [String] -> IO ()
initWorkers workers work
    | length workers == length work = do
        mapM (\((hin, hout, phdl, i), query) -> do hPutStr hin query; hFlush hin) (zip workers work)
        pure ()
    | otherwise = error "length of work and number of workers don't correspond!"

checkJobResult :: (Handle, Handle, ProcessHandle, Int) -> IO (Bool, String)
checkJobResult (hin, hout, ph, _) = do
    out <- readHandle hout ""
    case take 3 out of
        "sat"     -> pure (True, out)
        otherwise -> pure (False, out)
    where 
        readHandle hdl acc = do
            res <- catchIOError (read_ hdl) (handleErr) -- TODO: handle other error types ?
            case res of
                "" -> pure acc
                r  -> readHandle hdl (acc ++ r)
            where 
                handleErr = (\e -> if isEOFError e then pure "" else ioError e)
                read_ hdl = hWaitForInput hdl 0 >>= \case 
                    True  -> hGetLine hdl
                    False -> pure ""

            --hIsEOF hdl >>= \case
            --False -> do res <- hGetLine hdl; readHandle hdl (res ++ acc)
            --True -> pure acc -- do hClose hdl; pure "EOF"

-- TODO: maybe handle this better than just terminate...
cleanUpPool :: [(Handle, Handle, ProcessHandle, Int)] -> IO [()]
cleanUpPool [] = pure []
cleanUpPool ps = do
    mapM (\(hin, hout, ph, _) -> do terminateProcess ph) ps -- hClose hin; hClose hout; TODO: but what if already closed?

-- returns the query leading to sat... TODO: return the seq of transactions instead!
runOnPool :: [(Handle, Handle, ProcessHandle, Int)] -> [String] -> IO (Maybe String)
runOnPool ps (query:qs) = do
    i <- waitForJob ps
    checkJobResult (ps !! i) >>= \case
        (False, _) -> do
            enqueueJob ps i query
            runOnPool ps qs
        (True, out) -> do
            cleanUpPool ps
            pure $ Just out
runOnPool ps [] = do
    check_and_clean ps
    where 
        check_and_clean [] = pure Nothing
        check_and_clean (p:ps) = do
            i <- waitForJob [p]
            checkJobResult p >>= \case
                (False, _) -> check_and_clean ps
                (True, out) -> do 
                    cleanUpPool ps
                    pure $ Just out