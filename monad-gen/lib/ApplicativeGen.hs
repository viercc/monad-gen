{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ApplicativeGen(
  -- * Data
  genApplicativeDataFrom,

  -- * Raw
  genRawApplicativeDataFrom,
) where

import Data.Array ((!))
import Data.Array.Extra qualified as Array
import Data.FunctorShape
import Data.Map.Strict qualified as Map
import Data.Vector qualified as V

import MonoidData qualified as Monoid
import MonoidData (RawMonoidData (..), Signature, MonoidData (..))

import ModelFinder.Model
import ModelFinder.Term
import ModelFinder.Solver
import ModelFinder.Model.GuessMaskModel

import Data.Permutation (Permutation, applyPermutation)
import EquivalenceUtil (uniqueUpTo)

import ApplicativeData
import Control.Monad (guard)

genApplicativeDataFrom :: (Foldable f) => MonoidData (Shape f) -> [ApplicativeData f]
genApplicativeDataFrom monData = ApplicativeData env <$> genRawApplicativeDataFrom sig mon
  where
    env = _elemTable monData
    sig = lengthShape <$> env
    mon = _rawMonoidData monData

genRawApplicativeDataFrom :: Signature -> RawMonoidData -> [RawApplicativeData]
genRawApplicativeDataFrom sig mon = do
  guard $ isFeasibleMonoid sig mon
  let tables = completeTable sig mon <$> gen sig mon
  (leftFactorTable, rightFactorTable) <- upToIso sig mon tables
  let result =
        RawApplicativeData
          { _signature = sig,
            _baseMonoid = mon,
            _leftFactorTable = leftFactorTable,
            _rightFactorTable = rightFactorTable
          }
  pure result

isFeasibleMonoid :: Signature -> RawMonoidData -> Bool
isFeasibleMonoid sig mon = sizeEq && noImpossibleNat
  where
    n = V.length sig
    sizeEq = V.length sig == _monoidSize mon
    op i j = _multTable mon Array.! (i,j)
    noImpossibleNat = and $ do
      i <- [0 .. n - 1]
      j <- [0 .. n - 1]
      let -- For a definition of Applicative multiplication:
          --   (fx <*> fy = fz)
          -- lhsNull means either fx or fy contains no element
          lhsIsNull = (sig V.! i == 0) || (sig V.! j == 0)
          -- rhsNull means either fz contain no element
          rhsIsNull = (sig V.! op i j) == 0
      -- It is not possible to define (fx <*> fy = fz)
      -- if lhs is null but rhs is non-null.
      pure $ not lhsIsNull || rhsIsNull

data Fn a = LeftFactor Int Int a | RightFactor Int Int a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type E = Term Fn Int
type Defn = (Fn Int, Int)
type Eqn = (E,E)

type DefTable f x = Map.Map (f x) x

leftE, rightE :: Int -> Int -> Term Fn a -> Term Fn a
leftE i j e = fun (LeftFactor i j e)
rightE i j e = fun (RightFactor i j e)

makeEqUnitL, makeEqUnitR :: RawMonoidData -> Int -> Int -> Defn
makeEqUnitL mon i x = (LeftFactor i e x, x)
  where
    e = _unitElem mon
makeEqUnitR mon i x = (RightFactor e i x, x)
  where
    e = _unitElem mon

makeEqAssocLL, makeEqAssocLR, makeEqAssocRR :: RawMonoidData -> (Int, Int, Int) -> Int -> Eqn
makeEqAssocLL mon (i, j, k) x = 
    (leftE i jk (con x), leftE i j (leftE ij k (con x)))
  where
    ij = op i j
    jk = op j k
    op a b = _multTable mon ! (a, b)
makeEqAssocRR mon (i, j, k) x =
    (rightE ij k (con x), rightE j k (rightE i jk (con x)))
  where
    ij = op i j
    jk = op j k
    op a b = _multTable mon ! (a, b)
makeEqAssocLR mon (i, j, k) x =
  (leftE j k (rightE i jk (con x)),
   rightE i j (leftE ij k (con x)))
  where
    op a b = _multTable mon ! (a, b)
    ij = op i j
    jk = op j k

type ModelImpl = GuessMaskModel' (Fn Int) Int

genDefTables :: ModelImpl -> [Eqn] -> [Defn] -> [DefTable Fn Int]
genDefTables pmodel props defs = modelToDefTable <$> solveEqs props (Map.fromList defs) pmodel

modelToDefTable :: ModelImpl -> DefTable Fn Int
modelToDefTable = simpleGuesses . rawModel

makeModel :: Signature -> RawMonoidData -> ModelImpl
makeModel sig _ = GuessMaskModel guessFilter (newSimpleModel univ)
  where
    maxNumX = maximum (0 : V.toList sig)
    univ = [0 .. maxNumX - 1]

    guessFilter (LeftFactor i _ _) y = y < sig V.! i
    guessFilter (RightFactor _ j _) y = y < sig V.! j

gen :: Signature -> RawMonoidData -> [DefTable Fn Int]
gen sig mon = genDefTables (makeModel sig mon) assocEquations unitEquations
  where
    n = _monoidSize mon
    op a b = _multTable mon ! (a, b)

    unitEquations = do
      i <- [0 .. n - 1]
      let numX = sig V.! i
      x <- [0 .. numX - 1]
      [makeEqUnitL mon i x, makeEqUnitR mon i x]
    assocEquations = do
      i <- [0 .. n - 1]
      j <- [0 .. n - 1]
      k <- [0 .. n - 1]
      let ijk = op i (op j k)
          numX = sig V.! ijk
      x <- [0 .. numX - 1]
      [makeEqAssocLL mon (i, j, k) x, makeEqAssocRR mon (i, j, k) x, makeEqAssocLR mon (i, j, k) x]

completeTable :: Signature -> RawMonoidData
  -> DefTable Fn Int
  -> (FactorTable, FactorTable)
completeTable sig mon table = case (,) <$> leftTable <*> rightTable of
    Nothing -> error "incomplete table?"
    Just tabs -> tabs
  where
    n = _monoidSize mon
    op i j = _multTable mon ! (i, j)
    arrayRange = ((0, 0), (n - 1, n - 1))

    leftTable = Array.genArrayM arrayRange (\(i, j) -> V.generateM (sig V.! op i j) (\x -> Map.lookup (LeftFactor i j x) table))
    rightTable = Array.genArrayM arrayRange (\(i, j) -> V.generateM (sig V.! op i j) (\x -> Map.lookup (RightFactor i j x) table))


upToIso :: Signature -> RawMonoidData -> [(FactorTable, FactorTable)] -> [(FactorTable, FactorTable)]
upToIso sig mon = uniqueUpTo (shapeIsos ++ posIsos)
  where
    op i j = _multTable mon ! (i,j)
    shapeIsos = applyShapePermutation <$> Monoid.rawAutomorphisms sig mon
    posIsos = applyTransposition op <$> isoGenerators sig

applyShapePermutation :: Permutation -> (FactorTable, FactorTable) -> (FactorTable, FactorTable)
applyShapePermutation perm = applyBoth
  where
    p = applyPermutation perm
    apply tab = Array.array (Array.bounds tab) [ ((p i, p j), v) | ((i,j), v) <- Array.assocs tab ]
    applyBoth (tabL, tabR) = (apply tabL, apply tabR)

data Transposition = Transpose Int Int Int
    deriving Show

isoGenerators :: Signature -> [Transposition]
isoGenerators sig =
  [ Transpose i x (x + 1) | (i,n) <- lengths, x <- [0 .. n - 2]]
  where
    lengths = V.toList $ V.indexed sig

applyTransposition :: (Int -> Int -> Int) -> Transposition -> (FactorTable, FactorTable) -> (FactorTable, FactorTable)
applyTransposition op (Transpose k x y) (leftTable, rightTable) = (leftTable', rightTable')
  where
    tr z
      | z == x    = y
      | z == y    = x
      | otherwise = z
    swapVector vec = vec V.// [ (x, vec V.! y), (y, vec V.! x) ]

    leftTrans (i,j) = onRange . onDomain
      where
        onDomain | op i j == k = swapVector
                 | otherwise   = id
        onRange | i == k    = fmap tr
                | otherwise = id
    
    rightTrans (i,j) = onRange . onDomain
      where
        onDomain | op i j == k = swapVector
                 | otherwise   = id
        onRange | j == k    = fmap tr
                | otherwise = id
    leftTable' = Array.imap leftTrans leftTable
    rightTable' = Array.imap rightTrans rightTable
