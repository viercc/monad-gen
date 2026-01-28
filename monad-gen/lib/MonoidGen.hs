{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module MonoidGen(
  -- * Generate Monoids
  genMonoidsWithSig,
  genMonoidsForApplicative,
  genMonoidsForMonad,

  -- * Raw monoid generation
  genRawMonoids,
  genRawMonoidsForApplicative,
  genRawMonoidsForMonad,
) where

import Prelude hiding (Enum(..))

import Data.Maybe (mapMaybe)
import Data.Map (Map)
import qualified Data.Map.Lazy as Map
import qualified Data.Vector as V
import Data.Array (Array)
import qualified Data.Array.Extra as Array
import Data.Permutation
import EquivalenceUtil (uniqueUpTo)
import Data.PTraversable

import Data.FunctorShape
import Data.Finitary.Enum

import ModelFinder.Term
import ModelFinder.Model
import ModelFinder.Model.GuessMaskModel
import ModelFinder.Solver

import MonoidData

-- * Generation

genMonoidsWithSig :: (Enum a, Sig a) => [MonoidData a]
genMonoidsWithSig = MonoidData env <$> genRawMonoids sig
  where
    (env, sig) = makeEnv

genMonoidsForApplicative :: (PTraversable f) => [MonoidData (Shape f)]
genMonoidsForApplicative = MonoidData env <$> genRawMonoidsForApplicative sig
  where
    (env, sig) = makeEnv

genMonoidsForMonad :: (PTraversable f) => [MonoidData (Shape f)]
genMonoidsForMonad = MonoidData env <$> genRawMonoidsForMonad sig
  where
    (env, sig) = makeEnv

-- generation

countZeroes :: Signature -> Int
countZeroes = length . takeWhile (== 0) . V.toList

genRawMonoids :: Signature -> [RawMonoidData]
genRawMonoids sig = do
  let n = V.length sig
  e <- unitCandidates
  let mults = mapMaybe (multMapToArray n) (gen n e)
  mult <- upToIso sig e mults
  pure (RawMonoidData n e mult)
  where
    lengths = V.toList sig
    unitCandidates = [x | (x, lenX', lenX) <- zip3 [0 ..] (-1 : lengths) lengths, lenX' < lenX]

genRawMonoidsForApplicative :: Signature -> [RawMonoidData]
genRawMonoidsForApplicative sig = do
  let n = V.length sig
  e <- unitCandidates
  let mults = mapMaybe (multMapToArray n) (genForApplicative n (countZeroes sig) e)
  mult <- upToIso sig e mults
  pure (RawMonoidData n e mult)
  where
    lengths = V.toList sig
    unitCandidates
      | null sig       = []
      | all (== 0) sig = [0]
      | otherwise      = [x | (x, lenX', lenX) <- zip3 [0 ..] (-1 : lengths) lengths, lenX' < lenX]

genRawMonoidsForMonad :: Signature -> [RawMonoidData]
genRawMonoidsForMonad sig = do
  let n = V.length sig
  e <- unitCandidates
  let mults = mapMaybe (multMapToArray n) (genForMonad n (countZeroes sig) e)
  mult <- upToIso sig e mults
  pure (RawMonoidData n e mult)
  where
    lengths = V.toList sig
    unitCandidates = [x | (x, lenX', lenX) <- zip3 [0 ..] (0 : lengths) lengths, lenX' < lenX]

multMapToArray :: Int -> MultTable -> Maybe (Array (Int,Int) Int)
multMapToArray n multMap = Array.genArrayM ((0,0), (n - 1, n - 1)) (\(i,j) -> Map.lookup (M i j) multMap)

data M a = M !a !a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type MultTable = Map (M Int) Int

(|*|) :: Term M a -> Term M a -> Term M a
(|*|) x y = fun (M x y)

assocLaw :: Property M
assocLaw = Property $
  ForAll $ \x ->
    ForAll $ \y ->
      ForAll $ \z ->
        Equals ((con x |*| con y) |*| con z) (con x |*| (con y |*| con z))

type ModelImpl = GuessMaskModel' (M Int) Int

genDefTables :: Int -> (M Int -> Int -> Bool) -> Map (M Int) Int -> [MultTable]
genDefTables n guessFilter defs = modelToSolution <$> solve xs [assocLaw] defs model 
  where
    xs = [0 .. n - 1]
    model = GuessMaskModel {
      guessMask = guessFilter,
      rawModel = newSimpleModel xs }

modelToSolution :: ModelImpl -> MultTable
modelToSolution = simpleGuesses . rawModel

gen :: Int -> Int -> [MultTable]
gen n e = genDefTables n guessFilter (Map.fromList knownDefs)
  where
    xs = [0 .. n - 1]
    knownDefs = 
        [ (M e x, x) | x <- xs]
     ++ [ (M x e, x) | x <- xs]
    guessFilter _ _ = True

genForApplicative :: Int -> Int -> Int -> [MultTable]
genForApplicative n numZeroes e = genDefTables n guessFilter (Map.fromList knownDefs)
  where
    xs = [0 .. n - 1]
    knownDefs =
        [ (M e x, x) | x <- xs]
     ++ [ (M x e, x) | x <- xs]
    guessFilter (M x y) z
      = (x >= numZeroes) && (y >= numZeroes) || (z < numZeroes)

genForMonad :: Int -> Int -> Int -> [MultTable]
genForMonad n numZeroes e = genDefTables n guessFilter (Map.fromList knownDefs)
  where
    xs = [0 .. n - 1]
    zeroes = [0 .. numZeroes - 1]
    knownDefs =
        [ (M e x, x) | x <- xs]
     ++ [ (M x e, x) | x <- xs]
     ++ [ (M z x, z) | z <- zeroes, x <- xs ]

    guessFilter (M _ y) z = y >= numZeroes || (z < numZeroes)

-- * Quotienting out by isomorphisms

upToIso :: Signature -> Int -> [Array (Int,Int) Int] -> [Array (Int,Int) Int]
upToIso env e = uniqueUpTo isos
  where
    n = V.length env
    env' = distinctLabel env e
    isos = applyTranspose n <$> fixingGeneratorsSorted env'

applyTranspose :: Int -> Transposition -> Array (Int,Int) Int -> Array (Int,Int) Int
applyTranspose n p table =
  Array.array ((0,0), (n - 1, n - 1))
    [ ((tr p x, tr p y), tr p z) | ((x,y),z) <- Array.assocs table ]
