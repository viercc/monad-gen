{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ApplicativeData(
  -- * Dict
  ApplicativeDict(..),
  makeApplicativeDict,

  -- * Data
  ApplicativeData(..),

  -- * Applicative-preserving isomorphisms
  automorphisms,

  -- ** Serialize
  serializeApplicativeDataList,
  deserializeApplicativeDataList,

  -- * Raw
  RawApplicativeData(..),
  FactorTable,
  prettyRawApplicativeData,

  -- * Applicative laws for Raw
  prop_LeftUnit,
  prop_RightUnit,
  prop_LeftLeft,
  prop_RightRight,
  prop_LeftRight,
) where

import Data.Foldable (toList)
import Data.Tuple (swap)
import Data.FunctorShape
import Data.List (sort)

import Data.Array (Array, (!))
import Data.Array.Extra qualified as Array
import Data.Vector qualified as V
import Data.Map.Strict qualified as Map
import Data.PTraversable
import Data.Traversable.Extra (indices)
import Data.PTraversable.Extra (skolem)

import MonoidGen (RawMonoidData (..), makeEnv, prettyRawMonoidData, encodeRawMonoidData, decodeRawMonoidData)

import Isomorphism

import Data.Proxy (Proxy (..))
import Control.Monad (guard)
import Text.Read (readMaybe)
import Data.Finitary.Enum (enum)

data ApplicativeDict f = ApplicativeDict
  { _applicativePure :: forall a. a -> f a,
    _applicativeLiftA2 :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
  }

makeApplicativeDict :: forall f. (PTraversable f) => ApplicativeData f -> ApplicativeDict f
makeApplicativeDict (ApplicativeData table raw) =
  ApplicativeDict {_applicativePure = pure', _applicativeLiftA2 = liftA2'}
  where
    e = _unitElem $ _baseMonoid raw
    op = monoidOp raw
    leftFactor = leftFactorOp raw
    rightFactor = rightFactorOp raw

    reverseTable = Map.fromList (swap <$> V.toList (V.indexed table))
    pure' :: forall a. a -> f a
    pure' = case table V.! e of
      Shape u1 -> (<$ u1)

    liftA2' :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
    liftA2' h x y = z
      where
        as = toList x
        bs = toList y
        mx = reverseTable Map.! Shape x
        my = reverseTable Map.! Shape y
        mz = op mx my
        zi = case table V.! mz of
          Shape z1 -> indices z1
        cs i =
          let j = leftFactor mx my i
              k = rightFactor mx my i
           in h (as !! j) (bs !! k)
        z = cs <$> zi

data ApplicativeData f = ApplicativeData
  { _applicativeShapeTable :: V.Vector (Shape f),
    _rawApplicative :: RawApplicativeData
  }

deriving instance Eq (f Ignored) => Eq (ApplicativeData f)
deriving instance Ord (f Ignored) => Ord (ApplicativeData f)

-- ** Serialize/deserialize

signatureOf :: forall f proxy. PTraversable f => proxy f -> [Int]
signatureOf _ = lengthShape <$> (enum :: [Shape f])

serializeApplicativeDataList :: forall f. PTraversable f => [ApplicativeData f] -> [String]
serializeApplicativeDataList apData =
  show (signatureOf @f Proxy) : map (show . encodeApplicativeData) (sort apData)

deserializeApplicativeDataList :: forall f. PTraversable f => [String] -> Either String [ApplicativeData f]
deserializeApplicativeDataList [] = Left "No signature"
deserializeApplicativeDataList (sigStr : records) =
  do readSig
     traverse parseMonadData (zip [2..] records)
  where
    readSig :: Either String ()
    readSig = case readMaybe sigStr of
      Nothing -> Left "parse error at signature"
      Just sig
        | sig == expectedSig -> Right ()
        | otherwise -> Left "signature mismatch"

    expectedSig :: [Int]
    expectedSig = signatureOf (Proxy :: Proxy f)

    parseMonadData :: (Int, String) -> Either String (ApplicativeData f)
    parseMonadData (lineNo, str) = case readMaybe str of
      Nothing -> Left $ "parse error at line " ++ show lineNo
      Just code -> case decodeApplicativeData code of
        Nothing -> Left $ "non well-formed ApplicativeData at line " ++ show lineNo
        Just md -> Right md

type ApplicativeCode = (Int, [Int], [[Int]], [[Int]])

encodeApplicativeData :: ApplicativeData f -> ApplicativeCode
encodeApplicativeData (ApplicativeData _ raw) = (unitElem, multTable, leftFactor, rightFactor)
  where
    (unitElem, multTable) = encodeRawMonoidData (_baseMonoid raw)
    leftFactor = V.toList <$> Array.elems (_leftFactorTable raw)
    rightFactor = V.toList <$> Array.elems (_rightFactorTable raw)

decodeApplicativeData :: forall f. PTraversable f => ApplicativeCode -> Maybe (ApplicativeData f)
decodeApplicativeData (unitElem, multTable, leftFactor, rightFactor) = do
  rawMonoid <- decodeRawMonoidData n (unitElem, multTable)
  let factorLens = Array.assocs (factorLenTable rawMonoid)
  guard validLength
  leftFactor' <- Array.listArray ((0,0),(n-1,n-1)) <$>
    sequenceA (zipWith makeLeftFactor factorLens leftFactor)
  rightFactor' <- Array.listArray ((0,0),(n-1,n-1)) <$>
    sequenceA (zipWith makeRightFactor factorLens rightFactor)
  let rawApplicative = RawApplicativeData {
        _signature = sig,
        _baseMonoid = rawMonoid,
        _leftFactorTable = leftFactor',
        _rightFactorTable = rightFactor'
      }
  pure ApplicativeData{
      _applicativeShapeTable = env,
      _rawApplicative = rawApplicative
    }
  where
    (env, sig) = makeEnv lengthShape
    n = length sig
    tableRange = ((0,0),(n-1,n-1))

    factorLenTable rawMonoid = Array.genArray tableRange $
      \ij -> sig V.! (_multTable rawMonoid Array.! ij)
    
    makeLeftFactor ((i,_), m) ks
      | valid = Just (V.fromListN m ks)
      | otherwise = Nothing
      where
        targetLen = sig V.! i
        checkRange k = 0 <= k && k < targetLen
        valid = length ks == m && all checkRange ks
    makeRightFactor ((_,j), m) ks
      | valid = Just (V.fromListN m ks)
      | otherwise = Nothing
      where
        targetLen = sig V.! j
        checkRange k = 0 <= k && k < targetLen
        valid = length ks == m && all checkRange ks
    
    validLength =
      length leftFactor == n * n &&
      length rightFactor == n * n

-- * Raw applicatives

data RawApplicativeData = RawApplicativeData
  { _signature :: V.Vector Int,
    _baseMonoid :: RawMonoidData,
    _leftFactorTable :: FactorTable,
    _rightFactorTable :: FactorTable
  }
  deriving (Eq, Ord, Show)

type FactorTable = Array (Int, Int) (V.Vector Int)

prettyRawApplicativeData :: String -> RawApplicativeData -> [String]
prettyRawApplicativeData name raw =
  [ name ++ " = RawApplicative{" ] ++
  map indent (
    [ "Signature: " ++ show (_signature raw) ] ++
    prettyRawMonoidData "base" (_baseMonoid raw) ++
    [ "LeftFactor:" ] ++
    map indent (Array.prettyArray (_leftFactorTable raw)) ++
    [ "RightFactor:" ] ++
    map indent (Array.prettyArray (_rightFactorTable raw))
  ) ++
  ["}"]
  where
    indent = ("  " ++)

monoidOp :: RawApplicativeData -> Int -> Int -> Int
monoidOp raw = op
  where
    table = _multTable . _baseMonoid $ raw
    op i j = table ! (i, j)

leftFactorOp :: RawApplicativeData -> Int -> Int -> Int -> Int
leftFactorOp raw = leftFactor
  where
    table = _leftFactorTable raw
    leftFactor i j x = table ! (i, j) V.! x

rightFactorOp :: RawApplicativeData -> Int -> Int -> Int -> Int
rightFactorOp raw = rightFactor
  where
    table = _rightFactorTable raw
    rightFactor i j x = table ! (i, j) V.! x

prop_LeftUnit :: RawApplicativeData -> Bool
prop_LeftUnit raw = and result
  where
    sig = _signature raw
    n = V.length sig
    e = _unitElem . _baseMonoid $ raw
    leftFactor = leftFactorOp raw
    result = do
      i <- [0 .. n - 1]
      let numX = sig V.! i
      x <- [0 .. numX - 1]
      pure $ leftFactor i e x == x

prop_RightUnit :: RawApplicativeData -> Bool
prop_RightUnit raw = and result
  where
    sig = _signature raw
    n = V.length sig
    e = _unitElem . _baseMonoid $ raw
    rightFactor = rightFactorOp raw
    result = do
      i <- [0 .. n - 1]
      let numX = sig V.! i
      x <- [0 .. numX - 1]
      pure $ rightFactor e i x == x

prop_LeftLeft :: RawApplicativeData -> Bool
prop_LeftLeft raw = and result
  where
    sig = _signature raw
    n = V.length sig
    op = monoidOp raw
    leftFactor = leftFactorOp raw
    result = do
      i <- [0 .. n - 1]
      j <- [0 .. n - 1]
      k <- [0 .. n - 1]
      let ij = op i j
          jk = op j k
          numX = sig V.! op ij k
      x <- [0 .. numX - 1]
      pure $ leftFactor i j (leftFactor ij k x) == leftFactor i jk x

prop_RightRight :: RawApplicativeData -> Bool
prop_RightRight raw = and result
  where
    sig = _signature raw
    n = V.length sig
    op = monoidOp raw
    rightFactor = rightFactorOp raw
    result = do
      i <- [0 .. n - 1]
      j <- [0 .. n - 1]
      k <- [0 .. n - 1]
      let ij = op i j
          jk = op j k
          numX = sig V.! op ij k
      x <- [0 .. numX - 1]
      pure $ rightFactor j k (rightFactor i jk x) == rightFactor ij k x

prop_LeftRight :: RawApplicativeData -> Bool
prop_LeftRight raw = and result
  where
    sig = _signature raw
    n = V.length sig
    op = monoidOp raw
    leftFactor = leftFactorOp raw
    rightFactor = rightFactorOp raw
    result = do
      i <- [0 .. n - 1]
      j <- [0 .. n - 1]
      k <- [0 .. n - 1]
      let ij = op i j
          jk = op j k
          numX = sig V.! op ij k
      x <- [0 .. numX - 1]
      pure $ rightFactor i j (leftFactor ij k x) == leftFactor j k (rightFactor i jk x)

automorphisms :: PTraversable f => ApplicativeDict f -> [Iso f]
automorphisms apDict = result
  where
    pureData = _applicativePure apDict ()
    fk = sort (toList skolem)
    -- lhs is sorted, since fk is sorted
    lhs = (,) <$> fk <*> fk
    rhs = uncurry (_applicativeLiftA2 apDict (,)) <$> lhs

    isFixing iso = (iso1 iso pureData == pureData) && rhs == rhs'
      where
        rhs' = op' <$> lhs
        op' (fa, fb) = iso2 iso $ _applicativeLiftA2 apDict (,) (iso1 iso fa) (iso1 iso fb)

    allSubIsos = makePositionIso ++ makeShapeIso
    allIsos = foldr (liftA2 (<>)) [mempty] allSubIsos
    -- numAllIsos = product (length <$> allSubIsos)
    result = filter isFixing allIsos