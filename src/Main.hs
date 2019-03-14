{-# LANGUAGE LambdaCase #-}
module Main where

import           LetrecParser
import           LetrecTypes
import           LetrecEval
import           Control.Monad           hiding ( MonadPlus(..) )
import           System.IO
import           System.Exit

emptyEnv = EmptyEnv

reval :: String -> Result Val
reval s = case parse parseExpr s of
  (res, ""  ) : _ -> eval res emptyEnv
  (_  , rest) : _ -> raiseOtherError $ "Unexpected characters: " ++ rest
  []              -> raise EmptyExpr

reportResult (Success a) = print a
reportResult (Failure e) = putStrLn $ "Error: " ++ show e

repl :: IO ()
repl = do
  putStr "LETREC> "
  hFlush stdout
  done <- isEOF
  if done
  then do { putStrLn "Exiting."; exitSuccess }
  else do
    exp <- getLine
    if exp == "" then repl else reportResult $ reval exp
    repl

-- |Read, evaluate, print a file.
repf :: String -> IO ()
repf filename = do
  x <- openFile filename ReadMode
  y <- hGetContents x
  reportResult $ reval y
  
main :: IO ()
main = do
  putStrLn "Welcome to the LETREC interpreter. Control-d to exit."
  repl
