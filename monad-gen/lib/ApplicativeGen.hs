{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ApplicativeGen(
  -- * Dict
  ApplicativeDict(..),
  makeApplicativeDict,

  -- * Data
  ApplicativeData(..),
  genApplicativeData,
  genApplicativeDataFrom,

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
import Data.PTraversable.Extra (_indices, skolem)
import Data.Tuple (swap)
import Data.Vector qualified as V
import MonoidGen (RawMonoidData (..), Signature, genRawMonoidsForApplicative, makeEnv, prettyRawMonoidData, MonoidData (..), stabilizingPermutations, Permutation (..))
import Data.Equivalence.Monad
import Control.Exception (assert)
import Isomorphism
import Data.List (sort)

import ModelFinder.Sig.Mono
import ModelFinder.Expr
import ModelFinder.Solver
import qualified Data.Set as Set

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
          Shape z1 -> _indices z1
        cs i =
          let j = leftFactor mx my i
              k = rightFactor mx my i
           in h (as !! j) (bs !! k)
        z = cs <$> zi

data ApplicativeData f = ApplicativeData
  { _applicativeShapeTable :: V.Vector (Shape f),
    _rawApplicative :: RawApplicativeData
  }

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

-- * Raw applicatives

data RawApplicativeData = RawApplicativeData
  { _signature :: V.Vector Int,
    _baseMonoid :: RawMonoidData,
    _leftFactorTable :: FactorTable,
    _rightFactorTable :: FactorTable
  }
  deriving Show

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

type Expr' = Expr (Sig (Fn Int) Int) Int

type Equation' = Property (Sig (Fn Int) Int)

type DefTable f x = Map.Map (f x) x

leftE, rightE :: Int -> Int -> Expr' -> Expr'
leftE i j = lift1 (\e-> Sig (LeftFactor i j e))
rightE i j = lift1 (\e -> Sig (RightFactor i j e))

makeEqUnitL, makeEqUnitR :: RawMonoidData -> Int -> Int -> Equation'
makeEqUnitL mon i x = leftE i e (pure x) `evaluatesTo` x
  where
    e = _unitElem mon
makeEqUnitR mon i x = rightE e i (pure x) `evaluatesTo` x
  where
    e = _unitElem mon

makeEqAssocLL, makeEqAssocLR, makeEqAssocRR :: RawMonoidData -> (Int, Int, Int) -> Int -> Equation'
makeEqAssocLL mon (i, j, k) x = leftE i (op j k) (pure x) `equals` leftE i j (leftE (op i j) k (pure x))
  where
    op a b = _multTable mon ! (a, b)
makeEqAssocRR mon (i, j, k) x = rightE (op i j) k (pure x) `equals` rightE j k (rightE i (op j k) (pure x))
  where
    op a b = _multTable mon ! (a, b)
makeEqAssocLR mon (i, j, k) x =
  leftE j k (rightE i jk (pure x))
    `equals` rightE i j (leftE ij k (pure x))
  where
    op a b = _multTable mon ! (a, b)
    ij = op i j
    jk = op j k

genDefTables :: Model (Sig (Fn Int) Int) -> [Equation'] -> [DefTable Fn Int]
genDefTables model props = solve 10 model propsMap >>= constraintToSolution >>= pure . monoSolutionToMap
  where
    propsMap = Map.fromList (zip [0 :: Int ..] props)

makeModel :: Signature -> RawMonoidData -> (Fn Int -> [Int]) -> Model (Sig (Fn Int) Int)
makeModel sig mon guess = monoMakeModel . Map.fromList $ modelList
  where
    n = _monoidSize mon
    op i j = _multTable mon ! (i, j)
    modelList = do
      i <- [0 .. n - 1]
      j <- [0 .. n - 1]
      let numK = sig V.! op i j
      k <- [0 .. numK - 1]
      let leftF = LeftFactor i j k
          rightF = RightFactor i j k
      [ (leftF, Set.fromList (guess leftF)),
        (rightF, Set.fromList (guess rightF)) ]

gen :: Signature -> RawMonoidData -> [DefTable Fn Int]
gen sig mon = genDefTables (makeModel sig mon guess) equations
  where
    n = _monoidSize mon
    op i j = _multTable mon ! (i, j)
    equations = unitEquations ++ assocEquations
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

    guess (LeftFactor i _ _) = [0 .. (sig V.! i) - 1]
    guess (RightFactor _ j _) = [0 .. (sig V.! j) - 1]

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
      equateAll (applyShapePermutation <$> perms <*> [mm])
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