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

  -- ** Serialization
  serializeMonoidDataList,
  deserializeMonoidDataList,

  MonoidCode,
  encodeRawMonoidData,
  decodeRawMonoidData,

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
  automorphisms,

  -- * Internals
  makeEnv, fakeEnv,
) where

import Prelude hiding (Enum(..))

import Data.List (sortOn, sort)
import Data.Maybe (mapMaybe)

import Data.Map (Map)
import qualified Data.Map.Lazy as Map

import Data.PTraversable

import qualified Data.Vector as V
import Data.Array ((!), Array)
import qualified Data.Array.Extra as Array

import Data.FunctorShape
import Data.Finitary.Enum

import ModelFinder.Term
import ModelFinder.Model
import ModelFinder.Model.GuessMaskModel
import ModelFinder.Solver
import Text.Read (readMaybe)

import Data.Permutation
import EquivalenceUtil (uniqueUpTo)

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

serializeMonoidDataList :: (a -> Int) -> [MonoidData a] -> [String]
serializeMonoidDataList _ [] = []
serializeMonoidDataList sig mds@(d : _) =
  show (V.toList (V.map sig (_elemTable d)))
    : map (show . encodeRawMonoidData . _rawMonoidData) mds

deserializeMonoidDataList :: V.Vector a -> [String] -> Either String (V.Vector (a, Int), [MonoidData a])
deserializeMonoidDataList _ [] = Left "No signature"
deserializeMonoidDataList elemTable (sigStr : records) =
  do sig <- readSig
     let sigtab = V.zip elemTable sig
     rawMonoids <- traverse parseRawMonoidData (zip [2..] records)
     pure (sigtab, map (MonoidData elemTable) rawMonoids)
  where
    n :: Int
    n = V.length elemTable

    readSig :: Either String (V.Vector Int)
    readSig = case readMaybe sigStr of
      Nothing -> Left "parse error at signature"
      Just sig
        | n `lengthEq` sig -> Right $ V.fromListN n sig
        | otherwise -> Left "wrong length for the signarue"

    parseRawMonoidData :: (Int, String) -> Either String RawMonoidData
    parseRawMonoidData (lineNo, str) = case readMaybe str of
      Nothing -> Left $ "parse error at line " ++ show lineNo
      Just code -> case decodeRawMonoidData n code of
        Nothing -> Left $ "non well-formed MonadData at line " ++ show lineNo
        Just md -> Right md

type MonoidCode = (Int, [Int])

encodeRawMonoidData :: RawMonoidData -> MonoidCode
encodeRawMonoidData rmd = (_unitElem rmd, Array.elems (_multTable rmd))

decodeRawMonoidData :: Int -> MonoidCode -> Maybe RawMonoidData
decodeRawMonoidData n (unitElem, multTableList)
  | valid = Just result
  | otherwise = Nothing
  where
    multTable = Array.listArray ((0,0),(n-1,n-1)) multTableList
    result = RawMonoidData n unitElem multTable
    rangeCheck x = 0 <= x && x < n
    valid = rangeCheck unitElem
      && all rangeCheck multTableList
      && (n * n) `lengthEq` multTableList

-- Correctly lazy @n == length as@
lengthEq :: Int -> [a] -> Bool
lengthEq n as
  | n < 0 = False
  | n == 0 = null as
  | otherwise = case drop (n - 1) as of
      [_] -> True
      _ -> False

-- * Generation

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
  deriving (Eq, Ord, Show)

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

distinctLabel :: Signature -> Int -> Signature
distinctLabel sig e = sig V.// [(e, distinctVal)]
  where
    distinctVal = minimum sig - 1

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

-- * Automorphisms

automorphisms :: Signature -> RawMonoidData -> [Permutation]
automorphisms sig rawData = filter (isFixing tab) $ fixingPermutationsSorted sig'
  where
    e = _unitElem rawData
    tab = _multTable rawData
    sig' = distinctLabel sig e

isFixing :: Array (Int, Int) Int -> Permutation -> Bool
isFixing tab perm = tab == permuteTable perm tab

permuteTable :: Permutation -> Array (Int, Int) Int -> Array (Int, Int) Int
permuteTable perm tab = tab'
  where
    p = applyPermutation perm
    tab' = Array.array (Array.bounds tab) [ ((p i, p j), p k) | ((i, j), k) <- Array.assocs tab ]