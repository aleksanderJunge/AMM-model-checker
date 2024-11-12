{-# LANGUAGE LambdaCase #-}

module Netting.Symbolic.Concurrency where

import System.Process
import GHC.IO.Handle
import Control.Concurrent
import Data.List
import Data.Maybe
import Data.Tuple.Extra
import Control.Monad
import Control.Monad.Extra

-- TODO: doesn't read the process exit code, probably not the best solution!
waitForJob :: [(Handle, ProcessHandle, Int)] -> IO (Int)
waitForJob ps = do
    done <- findM (\(h, ph,i) -> getProcessExitCode ph >>= (pure . isJust)) ps
    case done of
        Nothing -> do 
            threadDelay 500 -- TODO: Find better solution than polling every 100 microseconds?
            waitForJob ps --termination not guaranteed, wonderful :D
        Just (h, ph, i)  -> pure i

-- this function takes a list, an int and a query and inserts a z3 query job on that index??
enqueueJob :: [(Handle, ProcessHandle, Int)] -> Int -> String -> IO ([(Handle, ProcessHandle, Int)])
enqueueJob ps i query =
    let (lefts, rights) = splitAt i ps
        filename = "/tmp/check_goal" ++ (show i) ++".smt2"
    in do
    newJob <- createJob i query
    pure $ lefts ++ [newJob] ++ (tail rights) -- tail rights is "safe" since we assume i < length ps

createJob :: Int -> String -> IO (Handle, ProcessHandle, Int)
createJob i query = do
    let filename = "/tmp/check_goal" ++ (show i) ++".smt2"
    writeFile filename query
    (_, Just hout, _, pHdl) <- createProcess (proc "z3" [filename]){std_out = CreatePipe}
    pure $ (hout, pHdl, i)

checkJobResult :: (Handle, ProcessHandle, Int) -> IO (Bool, String)
checkJobResult (h, ph, _) = do
    out <- readHandle h
    case take 3 out of
        "sat"     -> pure $ (True, out)
        otherwise -> pure $ (False, out)
    where 
        readHandle hdl = hIsEOF hdl >>= \case
            False -> do
                out <- hGetContents hdl
                pure out
            True -> do 
                hClose hdl
                pure "EOF"

cleanUpPool :: [(Handle, ProcessHandle, Int)] -> IO [()]
cleanUpPool [] = pure []
cleanUpPool ps = mapM terminateProcess (map snd3 ps) -- Stop waiting and just send terminate sig

managePool :: [(Handle, ProcessHandle, Int)] -> [String] -> IO (Maybe String)
managePool ps (query:qs) = do
    i <- waitForJob ps
    checkJobResult (ps !! i) >>= \case
        (False, _)  -> do
            ps' <- enqueueJob ps i query
            managePool ps' qs
        (True, out) -> do
            cleanUpPool ps
            pure $ Just out
managePool ps [] = do
    cleanUpPool ps
    pure Nothing