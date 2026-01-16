module Main (main) where

import ModelFinder.Examples.Group
    ( searchGroupOfOrder, prettyPrintSolution, searchGroupOfOrder' )

countGroups :: Int -> IO ()
countGroups n = putStrLn $ "count " ++ show n ++ " = " ++ show (length (searchGroupOfOrder n))

countGroups' :: Int -> IO ()
countGroups' n = putStrLn $ "count " ++ show n ++ " = " ++ show (length (searchGroupOfOrder' n))

main :: IO ()
main = do
  putStrLn "### Run Group example"
  putStrLn "Every group of order 4, unit = 0"
  mapM_ (prettyPrintSolution 4) $ searchGroupOfOrder 4
  putStrLn "### Run Group examples (length only)"
  countGroups 5
  putStrLn "### Run Group examples (length only) (custom Model)"
  countGroups' 5
  countGroups' 6
  countGroups' 7