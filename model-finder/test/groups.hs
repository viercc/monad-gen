module Main (main) where

import ModelFinder.Examples.Group
    ( searchGroupOfOrder, prettyPrintSolution )

main :: IO ()
main = do
  putStrLn "### Run Group example"
  putStrLn "Every group of order 4, unit = 0"
  mapM_ (prettyPrintSolution 4) $ searchGroupOfOrder 4
  putStrLn "### Run Group examples (length only)"
  let n = 5
  putStrLn $ "count " ++ show n ++ " = " ++ show (length (searchGroupOfOrder n))