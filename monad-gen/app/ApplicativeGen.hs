{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ApplicativeGen(
  ApplicativeDict(..),
  makeApplicativeDict,

  ApplicativeData(..),
  genApplicativeData,

  RawApplicativeData(..),
  prettyRawApplicativeData,
  prop_LeftUnit,
  prop_RightUnit,
  prop_LeftLeft,
  prop_RightRight,
  prop_LeftRight,

  genRawApplicatives
) where

import Data.Array (Array, (!))
import Data.Array.Extra qualified as Array
import Data.Foldable (toList)
import Data.FunctorShape
import Data.Map.Strict qualified as Map
import Data.PTraversable
import Data.PTraversable.Extra (_indices)
import Data.Tuple (swap)
import Data.Vector qualified as V
import EquationSolver
import MonoidGen (RawMonoidData (..), Signature, genRawMonoidsForApplicative, makeEnv, prettyRawMonoidData)

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
genApplicativeData = ApplicativeData env <$> genRawApplicatives sig
  where
    (env, sig) = makeEnv (length . unShape)

-- * Raw applicatives

data RawApplicativeData = RawApplicativeData
  { _signature :: V.Vector Int,
    _baseMonoid :: RawMonoidData,
    _leftFactorTable :: Array (Int, Int) (V.Vector Int),
    _rightFactorTable :: Array (Int, Int) (V.Vector Int)
  }
  deriving Show

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
rightFactorOp raw = leftFactor
  where
    table = _leftFactorTable raw
    leftFactor i j x = table ! (i, j) V.! x

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

genRawApplicatives :: Signature -> [RawApplicativeData]
genRawApplicatives sig = do
  mon <- genRawMonoidsForApplicative sig
  defTable <- gen sig mon
  Just (leftFactorTable, rightFactorTable) <- [completeTable sig mon defTable]
  let result =
        RawApplicativeData
          { _signature = sig,
            _baseMonoid = mon,
            _leftFactorTable = leftFactorTable,
            _rightFactorTable = rightFactorTable
          }
  pure result

data Fn a = LeftFactor Int Int a | RightFactor Int Int a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type Expr' = Expr Fn Int

type Equation' = Equation Fn Int

leftE, rightE :: Int -> Int -> Expr' -> Expr'
leftE i j e = Node (LeftFactor i j e)
rightE i j e = Node (RightFactor i j e)

makeEqUnitL, makeEqUnitR :: RawMonoidData -> Int -> Int -> Equation'
makeEqUnitL mon i x = leftE i e (Leaf x) `Equals` Leaf x
  where
    e = _unitElem mon
makeEqUnitR mon i x = rightE e i (Leaf x) `Equals` Leaf x
  where
    e = _unitElem mon

makeEqAssocLL, makeEqAssocLR, makeEqAssocRR :: RawMonoidData -> (Int, Int, Int) -> Int -> Equation'
makeEqAssocLL mon (i, j, k) x = leftE i (op j k) (Leaf x) `Equals` leftE i j (leftE (op i j) k (Leaf x))
  where
    op a b = _multTable mon ! (a, b)
makeEqAssocRR mon (i, j, k) x = rightE (op i j) k (Leaf x) `Equals` rightE j k (rightE i (op j k) (Leaf x))
  where
    op a b = _multTable mon ! (a, b)
makeEqAssocLR mon (i, j, k) x =
  leftE j k (rightE i jk (Leaf x))
    `Equals` rightE i j (leftE ij k (Leaf x))
  where
    op a b = _multTable mon ! (a, b)
    ij = op i j
    jk = op j k

type Table' = DefTable Fn Int

gen :: Signature -> RawMonoidData -> [Table']
gen sig mon = genDefTables guess equations
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

completeTable :: Signature -> RawMonoidData -> Table' -> Maybe (Array (Int, Int) (V.Vector Int), Array (Int, Int) (V.Vector Int))
completeTable sig mon table = (,) <$> leftTable <*> rightTable
  where
    n = _monoidSize mon
    op i j = _multTable mon ! (i, j)
    arrayRange = ((0, 0), (n - 1, n - 1))

    leftTable = Array.genArrayM arrayRange (\(i, j) -> V.generateM (sig V.! op i j) (\x -> Map.lookup (LeftFactor i j x) table))
    rightTable = Array.genArrayM arrayRange (\(i, j) -> V.generateM (sig V.! op i j) (\x -> Map.lookup (RightFactor i j x) table))