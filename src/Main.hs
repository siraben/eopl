{-|
Module      : Main
Description : The main entry point for LETREC.

Includes I/O for a REPL that repeatedly reads a string from the user,
evaluates and prints the result.
-}

{-# LANGUAGE LambdaCase #-}
module Main where

import           Control.Monad hiding (MonadPlus (..))
import           LetrecEval
import           LetrecParser
import           LetrecTypes
import           System.Exit
import           System.IO

-- |Parse and evaluate a string.
reval :: String -> Result Val
reval s = case parse parseExpr s of
  (res, ""  ) : _ -> eval res EmptyEnv
  (_  , rest) : _ -> raiseOtherError $ "Unexpected characters: " ++ rest
  []              -> raise EmptyExpr

-- |Print the contents of a value of type 'Result' 'Val', or an error
-- message.
reportResult :: Result Val -> IO ()
reportResult (Success a) = print a
reportResult (Failure e) = putStrLn $ "Error: " ++ show e

-- |The main REPL loop.
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

-- |The entry point for the LETREC REPL.
main :: IO ()
main = do
  putStrLn "Welcome to the LETREC interpreter. Control-d to exit."
  repl
