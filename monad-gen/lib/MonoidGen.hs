{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module MonoidGen(
  -- * Generate Monoids
  MonoidDict(..),
  makeMonoidDict,

  MonoidData(..),
  genMonoids,
  genMonoidsWithSig,
  genMonoidsForApplicative,
  genMonoidsForMonad,
  prettyMonoidData,

  -- * Raw monoids
  RawMonoidData(..),
  prettyRawMonoidData,

  -- * Raw monoid generation
  Signature,
  genRawMonoids,
  genRawMonoidsForApplicative,
  genRawMonoidsForMonad,

  -- * Permutations
  Permutation(..),
  stabilizingPermutations,

  -- * Internals
  makeEnv, fakeEnv,
) where

import Prelude hiding (Enum(..))

import Data.Equivalence.Monad
import Data.List (sortOn, sort, groupBy, permutations)
import Data.Maybe (mapMaybe)
import Data.Foldable (for_)

import Data.Map (Map)
import qualified Data.Map.Lazy as Map

import Data.PTraversable

import qualified Data.Vector as V
import Data.Array ((!), Array)
import qualified Data.Array.Extra as Array

import Data.FunctorShape
import Data.Finitary.Enum

--import EquationSolver
import Data.Function (on)

import ModelFinder.Term
import ModelFinder.Model
import ModelFinder.Model.GuessMaskModel
import ModelFinder.Solver

-- * MonoidDict

data MonoidDict a = MonoidDict
  { monoidUnit :: a,
    monoidMult :: a -> a -> a
  }

makeMonoidDict :: Ord a => MonoidData a -> MonoidDict a
makeMonoidDict
  MonoidData{
    _elemTable = env,
    _rawMonoidData = RawMonoidData {
      _unitElem = e,
      _multTable = mult
    }
  } = MonoidDict (env V.! e) op
  where
    revTable = Map.fromList [(f_, i) | (i, f_) <- V.toList (V.indexed env)]
    fromKey = (revTable Map.!)
    op f1 f2 = env V.! (mult ! (fromKey f1, fromKey f2))


-- * MonoidData

data MonoidData a = MonoidData
  {
    _elemTable :: V.Vector a,
    _rawMonoidData :: RawMonoidData
  }

genMonoids :: (Enum a) => [MonoidData a]
genMonoids = genMonoidsWithSig (const 1)

genMonoidsWithSig :: (Enum a) => (a -> Int) -> [MonoidData a]
genMonoidsWithSig f = MonoidData env <$> genRawMonoids sig
  where
    (env, sig) = makeEnv f

genMonoidsForApplicative :: (PTraversable f) => [MonoidData (Shape f)]
genMonoidsForApplicative = MonoidData env <$> genRawMonoidsForApplicative sig
  where
    (env, sig) = makeEnv (\(Shape f1) -> length f1)

genMonoidsForMonad :: (PTraversable f) => [MonoidData (Shape f)]
genMonoidsForMonad = MonoidData env <$> genRawMonoidsForMonad sig
  where
    (env, sig) = makeEnv (\(Shape f1) -> length f1)

prettyMonoidData :: (Show a) => String -> MonoidData a -> [String]
prettyMonoidData monName monoidData =
  [monName ++ " = Monoid{"] ++
  map ("  " ++) (
    [ "Elements:" ] ++
    map indent (prettyElems env) ++
    [ "Unit element: " ++ show e ] ++
    [ "Multiplication table: " ] ++
    map indent (Array.prettyArray (_multTable (_rawMonoidData monoidData)))
  ) ++
  ["}"]
  where
    env = _elemTable monoidData
    e = _unitElem (_rawMonoidData monoidData)
    indent = ("  " ++)

prettyElems :: (Show a) => V.Vector a -> [String]
prettyElems env = [ show i ++ " = " ++ show f_ | (i, f_) <- V.toList (V.indexed env) ]

makeEnv :: (Enum a) => (a -> Int) -> (V.Vector a, Signature)
makeEnv f = (keys, sigs)
  where
    (keys, sigs) = V.unzip $ V.fromList $ sortOn snd [(a, f a) | a <- enum]

fakeEnv :: [Int] -> Signature
fakeEnv ns = V.fromList (sort ns)

-- * RawMonoidData

data RawMonoidData = RawMonoidData {
  _monoidSize :: Int,
  _unitElem :: Int,
  _multTable :: Array (Int,Int) Int
  }
  deriving Show

prettyRawMonoidData :: String -> RawMonoidData -> [String]
prettyRawMonoidData monName raw =
  [monName ++ " = RawMonoid{"] ++
  map ("  " ++) (
    [ "Elements: [0 .. " ++ show (n - 1) ++ "]" ] ++
    [ "Unit element: " ++ show (_unitElem raw) ] ++
    [ "Multiplication table: " ] ++
    map indent (Array.prettyArray (_multTable raw))
  ) ++
  ["}"]
  where
    n = _monoidSize raw
    indent = ("  " ++)

-- generation

type Signature = V.Vector Int

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

type ModelImpl = GuessMaskModel M Int (SimpleModel M Int)

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

upToIso :: Signature -> Int -> [Array (Int,Int) Int] -> [Array (Int,Int) Int]
upToIso env e tabs = runEquivM id min $ do
  for_ tabs $ \mm -> do
    equate mm mm
  for_ (isoGenerators env e) $ \tr ->
    for_ tabs $ \mm -> equate mm (applyTranspose n tr mm)
  classes >>= traverse desc
  where
    n = V.length env

data Transposition = Transpose Int Int
  deriving (Show)

isoGenerators :: Signature -> Int -> [Transposition]
isoGenerators sig e =
  [Transpose i j | ((i, n), (j, m)) <- zip lengths' (drop 1 lengths'), n == m]
  where
    lengths = V.toList $ V.indexed sig
    lengths' = filter ((/= e) . fst) lengths

applyTranspose :: Int -> Transposition -> Array (Int,Int) Int -> Array (Int,Int) Int
applyTranspose n (Transpose a b) table =
  Array.array ((0,0), (n - 1, n - 1))
    [ ((tr x, tr y), tr z) | ((x,y),z) <- Array.assocs table ]
  where
    tr i
      | i == a = b
      | i == b = a
      | otherwise = i


newtype Permutation = MkPermutation (V.Vector Int)
   deriving (Eq, Ord, Show)

stabilizingPermutations :: Signature -> RawMonoidData -> [[Permutation]]
stabilizingPermutations sig rawData = filter nonTrivial $ filter (isFixing tab) . subPermutations n <$> permGroups sig e
  where
    n = _monoidSize rawData
    e = _unitElem rawData
    tab = _multTable rawData
    nonTrivial = (> 1) . length

permGroups :: Eq a => V.Vector a -> Int -> [[Int]]
permGroups sig e = groups
  where
    lengths = V.toList $ V.indexed sig
    lengths' = filter ((/= e) . fst) lengths
    groups = fmap fst <$> groupBy ((==) `on` snd) lengths'

subPermutations :: Int -> [Int] -> [Permutation]
subPermutations n xs = MkPermutation <$> [ iota V.// zip xs ys | ys <- permutations xs ]
  where
    iota = V.generate n id

isFixing :: Array (Int, Int) Int -> Permutation -> Bool
isFixing tab perm = tab == applyPermutation perm tab

applyPermutation :: Permutation -> Array (Int, Int) Int -> Array (Int, Int) Int
applyPermutation (MkPermutation permVector) tab = tab'
  where
    p = (permVector V.!)
    tab' = Array.array (Array.bounds tab) [ ((p i, p j), p k) | ((i, j), k) <- Array.assocs tab ]