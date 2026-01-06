module Main (main) where

import ModelFinder.Dependent.Examples.Monad ( searchMonad )

main :: IO ()
main = do
  putStrLn "### Run Monad example"
  putStrLn $ "Number of models = " ++ show (length (searchMonad ()))
  putStrLn "(expected 12)"
