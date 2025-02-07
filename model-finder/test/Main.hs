module Main (main) where

import ModelFinder.Examples.Monad ( searchMonad )
import ModelFinder.Examples.Group
    ( searchGroupOfOrder, prettyPrintSolution )

main :: IO ()
main = do
  putStrLn "### Run Group example"
  putStrLn "Every group of order 4, unit = 0"
  mapM_ (prettyPrintSolution 4) $ searchGroupOfOrder 4
  putStrLn "### Run Monad example"
  putStrLn $ "Number of models = " ++ show (length (searchMonad ()))
  putStrLn "(expected 12)"
