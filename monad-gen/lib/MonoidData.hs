module MonoidData(
  -- * Monoid data
  MonoidDict(..),
  makeMonoidDict,

  MonoidData(..),
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
  makeEnv, fakeEnv,
  distinctLabel,

  -- * Permutations
  automorphisms,

) where

import Prelude hiding (Enum(..))

import Data.List (sortOn, sort)
import qualified Data.Map.Lazy as Map

import qualified Data.Vector as V
import Data.Array ((!), Array)
import qualified Data.Array.Extra as Array

import Data.Finitary.Enum
import Text.Read (readMaybe)
import Data.Permutation

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
  deriving (Eq, Ord)

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

makeEnv :: (Enum a) => (a -> Int) -> (V.Vector a, Signature)
makeEnv f = (keys, sigs)
  where
    (keys, sigs) = V.unzip $ V.fromList $ sortOn snd [(a, f a) | a <- enum]

fakeEnv :: [Int] -> Signature
fakeEnv ns = V.fromList (sort ns)

-- * Quotienting out by isomorphisms

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

distinctLabel :: Signature -> Int -> V.Vector Int
distinctLabel sig e = sig V.// [(e, distinctVal)]
  where
    distinctVal = minimum sig - 1
