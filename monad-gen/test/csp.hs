module Main(main) where

import System.Exit (exitFailure)
import qualified System.IO as IO
import qualified Data.Map as Map
import Data.List (sort)

import CSP
import qualified Data.Foldable as F
import Control.Monad (unless)

shouldBe :: (Show a, Eq a) => a -> a -> IO ()
shouldBe actual expected
  | actual == expected = pure ()
  | otherwise = do
      IO.hPutStrLn IO.stderr $ "actual:   " ++ show actual
      IO.hPutStrLn IO.stderr $ "expected: " ++ show expected
      exitFailure

-- | Check solutions against expected solutions set
expect :: Variables -> [Constraint] -> [[(VarName,Int)]] -> IO ()
expect vars cons expected = do
  let allVars = Map.keysSet vars
  solutions <- solveCSP vars cons allVars
  let solutionsSorted = Map.toList <$> sort solutions
      expectedSorted = fmap Map.toList . sort . fmap Map.fromList $ expected
  solutionsSorted `shouldBe` expectedSorted

-- | Check number of solutions against expected number
expectNum :: Variables -> [Constraint] -> Int -> IO ()
expectNum vars cons expected = do
  let allVars = Map.keysSet vars
  solutions <- solveCSP vars cons allVars
  length solutions `shouldBe` expected

-- | Check solutions against brute-force solver
test :: Variables -> [Constraint] -> IO ()
test vars cons = do
  let allVars = Map.keysSet vars
      expected = sort $ solveCSPBruteForce vars cons allVars
  solutions <- solveCSP vars cons allVars
  let solutionsSorted = sort solutions
      expectedSorted = sort expected
  solutionsSorted `shouldBe` expectedSorted

main :: IO ()
main = do
  putStrLn "Variable Encoding"
  -- No constraint => enumerate all values
  expect (Map.fromList [("x", VarRange 0 4)]) []
    [[("x",0)], [("x",1)], [("x",2)], [("x",3)]]
  -- Singleton range => just it
  expect (Map.fromList [("x", VarRange 0 1), ("y", VarRange 2 3)]) []
    [[("x",0), ("y",2)]]
  -- Contain empty range => unsat
  expect (Map.fromList [("x", VarRange 0 4), ("y", VarRange 2 2)]) []
    []
  
  putStrLn "Never"
  expect (Map.fromList [("x", VarRange 0 1), ("y", VarRange 2 3)]) [never] []

  putStrLn "VarImmEq"
  expect (Map.fromList [("x", VarRange 0 4)]) ["x" %==. 2]
    [[("x",2)]]
  expect (Map.fromList [("x", VarRange 0 4)]) ["x" %==. (-1)]
    []
  expect (Map.fromList [("x", VarRange 0 4)]) ["x" %==. 4]
    []
  
  putStrLn "VarImmNe"
  expect (Map.fromList [("x", VarRange 3 8)]) ["x" %/=. 5]
    [[("x",3)], [("x",4)], [("x",6)], [("x",7)]]
  expect (Map.fromList [("x", VarRange 3 8)]) ["x" %/=. 1]
    [[("x",3)], [("x",4)], [("x",5)], [("x",6)], [("x",7)]]
  expect (Map.fromList [("x", VarRange 3 8)]) ["x" %/=. 2]
    [[("x",3)], [("x",4)], [("x",5)], [("x",6)], [("x",7)]]
  expect (Map.fromList [("x", VarRange 3 8)]) ["x" %/=. 8]
    [[("x",3)], [("x",4)], [("x",5)], [("x",6)], [("x",7)]]
  expect (Map.fromList [("x", VarRange 3 8)]) ["x" %/=. 10]
    [[("x",3)], [("x",4)], [("x",5)], [("x",6)], [("x",7)]]

  putStrLn "VarPred"
  expect (Map.fromList [("x", VarRange 0 10)]) ["x" `satisfy` even]
    [[("x",0)], [("x",2)], [("x",4)], [("x",6)], [("x",8)]]
  expect (Map.fromList [("x", VarRange 0 10)]) ["x" `satisfy` const False]
    []
  
  putStrLn "VarVarEq"
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 0 3)]) ["x" %==% "y"]
    [[("x",0),("y",0)], [("x",1),("y",1)], [("x",2),("y",2)]]
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 1 5)]) ["x" %==% "y"]
    [[("x",1),("y",1)], [("x",2),("y",2)]]
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 3 4)]) ["x" %==% "y"]
    []
  
  putStrLn "VarVarNe"
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 0 2)]) ["x" %/=% "y"]
    [[("x",0),("y",1)], [("x",1),("y",0)], [("x",2),("y",0)], [("x",2),("y",1)]]
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 0 2)]) ["x" %/=% "y", "x" %==% "y"]
    []
  test (Map.fromList [("x", VarRange 0 4), ("y", VarRange 0 4)]) ["x" %/=% "y"]

  putStrLn "VarVarLe"
  expectNum (Map.fromList [("x", VarRange 0 3), ("y", VarRange 3 6)]) ["x" %<=% "y"] 9
    -- Disjoint case (always true)
  expectNum (Map.fromList [("x", VarRange 0 3), ("y", VarRange 3 6)]) ["y" %<=% "x"] 0
    -- Disjoint case (always false)
  expectNum (Map.fromList [("x", VarRange 0 3), ("y", VarRange 0 3)]) ["x" %<=% "y"]
    (3 * 4 `div` 2)
  expectNum (Map.fromList [("x", VarRange 0 3), ("y", VarRange 0 3), ("z", VarRange 0 3)])
    ["x" %<=% "y", "y" %<=% "z"]
    ((3 * 4 * 5) `div` 6)
  test (Map.fromList [("x", VarRange 0 4), ("y", VarRange 0 4)]) ["x" %<=% "y"]

  putStrLn "FunVarEq"
  let cycle3 x = (x + 1) `mod` 3
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 0 3)]) [functionEq cycle3 "x" "y"]
    [[("x",0),("y",1)],[("x",1),("y",2)],[("x",2),("y",0)]]
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 2 4)]) [functionEq (4 *) "x" "y"]
    []
  
  putStrLn "Dependent"
  let dep1 x = if x == 0 then "y" %==. 1 else "y" %==. 2
  expect (Map.fromList [("x", VarRange 0 3), ("y", VarRange 0 3)]) [depend "x" >>= dep1]
    [[("x",0),("y",1)], [("x",1),("y",2)], [("x",2),("y",2)]]
  
  putStrLn "Pidgeonhole Unsat"
  expect (Map.fromList [("p0", VarRange 0 2), ("p1", VarRange 0 2), ("p2", VarRange 0 2)])
    ["p0" %/=% "p1", "p1" %/=% "p2", "p0" %/=% "p2"]
    []
  
  putStrLn "Graph Coloring"
  testGraphColoring 3 3 [(0,1), (1,2), (0,2)]
  testGraphColoring 3 2 [(0,1), (1,2)]
  testGraphColoring 4 2 [(0,1), (1,2), (2,3), (3,0)]
  testGraphColoring 5 2 [(0,1), (1,2), (2,3), (3,4), (4,0)]

  putStrLn "NQueens"
  uncurry expectNum (defineNQueens 4) 2
  uncurry test (defineNQueens 5)

testGraphColoring :: Int -> Int -> [(Int,Int)] -> IO ()
testGraphColoring n k edges = graphValidity >> test vars cons
  where
    graphValidity =
      F.for_ edges $ \(i,j) ->
        unless (0 <= i && i < n && 0 <= j && j < n && i /= j) $
          IO.hPutStrLn IO.stderr $ "Bad edge:" ++ show (i,j) ++ " in graph of n=" ++ show n
    var i = "p" ++ show i
    vars = Map.fromList [ (var i, VarRange 0 k) | i <- [0 .. n - 1] ]
    cons = [ var i %/=% var j | (i,j) <- edges ]

defineNQueens :: Int -> (Variables, [Constraint])
defineNQueens n = (vars, cons)
  where
    -- q_i ∈ [0, n] "i-th queen is on rank i and at file q_i"
    var i = "q" ++ show i
    vars = Map.fromList [ (var i, VarRange 0 n) | i <- [0 .. n - 1]]

    -- "i-th queen doesn't hit j-th queen, i > j"
    cons = [queenDoesn'tHit i j | i <- [0 .. n - 1], j <- [0 .. i - 1]]
    queenDoesn'tHit i j =
      let d = i - j
      in depend (var i) >>= \qi -> var j `satisfy` \qj ->
           (qi /= qj) && (qi + d /= qj) && (qi - d) /= qj