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
  -- * Dict
  ApplicativeDict(..),
  makeApplicativeDict,

  -- * Data
  ApplicativeData(..),
  genApplicativeData,
  genApplicativeDataFrom,

  -- ** Serialize
  serializeApplicativeDataList,
  deserializeApplicativeDataList,

  -- * Raw
  RawApplicativeData(..),
  prettyRawApplicativeData,
  genRawApplicativeData,
  genRawApplicativeDataFrom,

  -- * Applicative laws for Raw
  prop_LeftUnit,
  prop_RightUnit,
  prop_LeftLeft,
  prop_RightRight,
  prop_LeftRight,

  -- * Applicative-preserving isomorphisms
  stabilizingIsomorphisms
) where

import Data.Array (Array, (!))
import Data.Array.Extra qualified as Array
import Data.Foldable (toList, for_)
import Data.FunctorShape
import Data.Map.Strict qualified as Map
import Data.PTraversable
import Data.Traversable.Extra (indices)
import Data.PTraversable.Extra (skolem)
import Data.Tuple (swap)
import Data.Vector qualified as V
import MonoidGen (RawMonoidData (..), Signature, genRawMonoidsForApplicative, makeEnv, prettyRawMonoidData, MonoidData (..), stabilizingPermutations, Permutation (..), encodeRawMonoidData, decodeRawMonoidData)
import Data.Equivalence.Monad
import Control.Exception (assert)
import Isomorphism
import Data.List (sort)

import ModelFinder.Model
import ModelFinder.Term
import ModelFinder.Solver
import ModelFinder.Model.GuessMaskModel
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

genApplicativeData :: PTraversable f => [ApplicativeData f]
genApplicativeData = ApplicativeData env <$> genRawApplicativeData sig
  where
    (env, sig) = makeEnv lengthShape

genApplicativeDataFrom :: (Foldable f) => MonoidData (Shape f) -> [ApplicativeData f]
genApplicativeDataFrom monData = ApplicativeData env <$> genRawApplicativeDataFrom sig mon
  where
    env = _elemTable monData
    sig = lengthShape <$> env
    mon = _rawMonoidData monData

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

genRawApplicativeData :: Signature -> [RawApplicativeData]
genRawApplicativeData sig = do
  mon <- genRawMonoidsForApplicative sig
  genRawApplicativeDataFrom sig mon

genRawApplicativeDataFrom :: Signature -> RawMonoidData -> [RawApplicativeData]
genRawApplicativeDataFrom sig mon = do
  let tables = completeTable sig mon <$> gen sig mon
  (leftFactorTable, rightFactorTable) <- upToIso sig mon tables
  let result =
        RawApplicativeData
          { _signature = sig,
            _baseMonoid = mon,
            _leftFactorTable = leftFactorTable,
            _rightFactorTable = rightFactorTable
          }
  -- sanity check
  let checkAll = prop_LeftUnit result && prop_RightUnit result &&
        prop_LeftLeft result && prop_LeftRight result && prop_RightRight result
  assert checkAll (pure ())
  pure result

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
upToIso sig mon tabs = runEquivM id min $ do
  for_ tabs $ \mm -> do
    equate mm mm
  for_ tabs $ \mm -> do
    for_ (stabilizingPermutations sig mon) $ \perms ->
      equateAll (mm : (applyShapePermutation <$> perms <*> [mm]))
    equateAll (mm : (applyTransposition op <$> isoGenerators sig <*> [mm]))
  classes >>= traverse desc
  where
    op i j = _multTable mon ! (i,j)

applyShapePermutation :: Permutation -> (FactorTable, FactorTable) -> (FactorTable, FactorTable)
applyShapePermutation (MkPermutation permVector) = applyBoth
  where
    p = (permVector V.!)
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

stabilizingIsomorphisms :: PTraversable f => ApplicativeDict f -> [Iso f]
stabilizingIsomorphisms apDict = result
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