module Main (main) where

import ModelFinder.Examples.Monad

main :: IO ()
main = do
  putStrLn "Run Monad example"
  putStrLn $ "# of model = " ++ show (length (searchMonad ()))
  putStrLn "(expected 12)"
