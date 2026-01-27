{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

module MonadGen.BinaryJoin(
  BinaryJoin(..),
  genFromApplicative,
  gen,
  binaryJoinToJoin
) where

import Control.Monad (guard)
import Data.Foldable (Foldable(toList))

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Bool (bool)
import Data.Bits

import qualified Data.PreNatMap as PNM
import Data.PreNatMap (PreNatMap)

import Data.FunctorShape
import ModelFinder.Model ( Model(..) )
import ModelFinder.Term
import ModelFinder.Solver

import Data.Traversable.Extra (indices)
import Data.PTraversable.Extra (shapes, skolem)

import GHC.Generics ((:.:) (..))
import ApplicativeData (ApplicativeDict(..))
import Data.PTraversable (PTraversable, enum1)
import ModelFinder.Model.PreNatMapModel
import Data.Bifunctor (Bifunctor(..))

-- * BinaryJoin operation

-- * Signature of join
data J x = J x x x
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

j :: Term J x -> Term J x -> Term J x -> Term J x
j x y0 y1 = fun (J x y0 y1)

-- Associativity of j
assocEqs :: PTraversable f => [(Term J (f Bool), Term J (f Bool))]
assocEqs = assocEq <$> f2 <*> f2 <*> f2 <*> f2 <*> f2
  where
    f2 = con <$> enum1 [False, True]
    assocEq x y0 y1 z0 z1 = (lhs, rhs)
      where
        lhs = j (j x y0 y1) z0 z1
        rhs = j x (j y0 z0 z1) (j y1 z0 z1)

-- naturality w.r.t. not
notEqs :: PTraversable f => [(Term J (f Bool), Term J (f Bool))]
notEqs = do
  x <- f2
  let x' = not <$> x
  guard (x <= x')
  notEq (con x) (con x') <$> (con <$> f2) <*> (con <$> f2)
  where
    f2 = enum1 [False, True]
    notEq x x' y0 y1 = (j x y0 y1, j x' y1 y0)

-- naturality w.r.t. constant join
constEqs :: PTraversable f => [(Term J (f Bool), Term J (f Bool))]
constEqs = constEq <$> f1 <*> f2 <*> f2
  where
    f1 = con <$> enum1 [False]
    f2 = con <$> enum1 [False, True]
    constEq x y0 y1 = (j x y0 y1, j x y0 y0)

-- left unit law
unitLeftDefs :: (PTraversable f) => Shape f -> Map.Map (J (f Bool)) (f Bool)
unitLeftDefs (Shape u_) = Map.fromList $ unitLeftDef <$> f2 <*> f2
  where
    u = False <$ u_
    f2 = enum1 [False, True]
    unitLeftDef y0 y1 = (J u y0 y1, y0)

-- right unit law
unitRightDefs :: (PTraversable f) => Shape f -> Map.Map (J (f Bool)) (f Bool)
unitRightDefs (Shape u_) = Map.fromList $ unitRightDef <$> f2
  where
    u0 = False <$ u_
    u1 = True <$ u_
    f2 = enum1 [False, True]
    unitRightDef x = (J x u0 u1, x)

-- Special case for an empty value
zeroDefs :: (PTraversable f) => Map.Map (J (f Bool)) (f Bool)
zeroDefs = Map.fromList $ zeroDef <$> f0 <*> f2 <*> f2
  where
    f0 = enum1 []
    f2 = enum1 [False, True]
    zeroDef z y0 y1 = (J z y0 y1, z)

apDefs :: forall f. (PTraversable f) => ApplicativeDict f -> Map.Map (J (f Bool)) (f Bool)
apDefs apDict = Map.fromList $ concat $ jAp <$> f2 <*> fi
  where
    f2 = enum1 [False, True]
    fi = toList skolem
    
    _liftA2 :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
    _liftA2 = _applicativeLiftA2 apDict 

    jAp x y = do
      (bitmap0, y0) <- boolTable y
      (bitmap1, y1) <- boolTable y
      let op b = testBit (bool bitmap0 bitmap1 b)
          lhs = J x y0 y1
          rhs = _liftA2 op x y
      [(lhs, rhs)]

-- Known definitions from Applicative

data BinaryJoin f a = BJ (f Bool) (f a) (f a)
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (f Bool), Show (f x)) => Show (BinaryJoin f x)
deriving instance (Eq (f Bool), Eq (f x)) => Eq (BinaryJoin f x)
deriving instance (Ord (f Bool), Ord (f x)) => Ord (BinaryJoin f x)

b2i :: Bool -> Int
b2i = bool 0 1

i2b :: Int -> Bool
i2b = (/= 0)

fromJ :: Functor f => J (f Bool) -> BinaryJoin f Int
fromJ (J x y0 y1) = b2i <$> BJ x y0 y1

-- * Model for BinaryJoin

newtype BinaryJoinModel f = BinaryJoinModel
  {
    joinPreNatMapModel :: PreNatMapModel (BinaryJoin f) f
  }

deriving instance (forall x. Show x => Show (f x), Traversable f) => Show (BinaryJoinModel f)

instance (Traversable f, (forall a. Ord a => Ord (f a))) => Model (J (f Bool)) (f Bool) (BinaryJoinModel f) where
  guess query (BinaryJoinModel m) = fmap i2b <$> guess (fromJ query) m

  guessMany queries (BinaryJoinModel m) = fmap i2b <$> guessMany (fromJ <$> queries) m

  enterDef js rhs (BinaryJoinModel m) = postproc <$> enterDef js' rhs' m
    where
      js' = fromJ <$> js
      rhs' = b2i <$> rhs
      postproc = bimap BinaryJoinModel (>>= makeBinaryJoinDefs)

  enterEqs js (BinaryJoinModel m) = postproc <$> enterEqs js' m
    where
      js' = fromJ <$> js
      postproc = bimap BinaryJoinModel (>>= makeBinaryJoinDefs)

makeBinaryJoinDefs :: Traversable f => (BinaryJoin f any, f Int) -> [(J (f Bool), f Bool)]
makeBinaryJoinDefs (bj, rhs) =
  do (bitmap, BJ x y0 y1) <- boolTable bj
     let rhsBool = testBit bitmap <$> rhs
     pure (J x y0 y1, rhsBool)

-- * Generation logic

-- >>> genFromPure (Shape (Just ()))
-- [make [PreEntry (BJ Nothing Nothing Nothing) Nothing,PreEntry (BJ Nothing Nothing (Just 0)) Nothing,PreEntry (BJ Nothing (Just 0) Nothing) Nothing,PreEntry (BJ Nothing (Just 0) (Just 1)) Nothing,PreEntry (BJ (Just False) Nothing Nothing) Nothing,PreEntry (BJ (Just False) Nothing (Just 0)) Nothing,PreEntry (BJ (Just False) (Just 0) Nothing) (Just 0),PreEntry (BJ (Just False) (Just 0) (Just 1)) (Just 0),PreEntry (BJ (Just True) Nothing Nothing) Nothing,PreEntry (BJ (Just True) Nothing (Just 0)) (Just 0),PreEntry (BJ (Just True) (Just 0) Nothing) Nothing,PreEntry (BJ (Just True) (Just 0) (Just 1)) (Just 1)]]

genFromPure :: forall f. (PTraversable f, Show (f Bool)) => Shape f -> [PreNatMap (BinaryJoin f) f]
genFromPure pureShape = pnmGuesses . joinPreNatMapModel <$> solveEqs allEqs allDefs model0
  where
    fShapes = Shape <$> shapes
    model0 = BinaryJoinModel $ PreNatMapModel { allShapes = Set.fromList fShapes, pnmGuesses = PNM.empty }
    allEqs = constEqs ++ notEqs ++ assocEqs
    allDefs = Map.unions [unitLeftDefs pureShape, unitRightDefs pureShape, zeroDefs]

gen :: forall f. (PTraversable f, Show (f Bool)) => [PreNatMap (BinaryJoin f) f]
gen = shapes >>= genFromPure . Shape

genFromApplicative :: forall f. (PTraversable f, Show (f Bool)) => ApplicativeDict f -> [PreNatMap (BinaryJoin f) f]
genFromApplicative apDict = pnmGuesses . joinPreNatMapModel <$> solveEqs allEqs allDefs model0
  where
    fShapes = Shape <$> shapes
    model0 = BinaryJoinModel $ PreNatMapModel { allShapes = Set.fromList fShapes, pnmGuesses = PNM.empty }
    allEqs = constEqs ++ notEqs ++ assocEqs
    allDefs = Map.unions [apDefs apDict, zeroDefs]

binaryJoinToJoin :: (Traversable f, (forall a. Ord a => Ord (f a))) => PreNatMap (BinaryJoin f) f -> PreNatMap (f :.: f) f
binaryJoinToJoin binaryJoinData = PNM.make (buildEntry <$> PNM.toEntries binaryJoinData)
  where
    buildEntry (BJ x y0 y1, rhs) = (Comp1 (bool y0 y1 <$> x), rhs)

-- Utilities

type Bitmap = Word

boolTable :: Traversable f => f any -> [(Bitmap, f Bool)]
boolTable f
  | n <= lenMax = mk <$> [0 .. 2 ^ n - 1]
  | otherwise = error $ "too long: " ++ show n ++ " >= " ++ show lenMax
  where
    lenMax = finiteBitSize (0 :: Word) `div` 2
    n = length f
    fi = indices f
    mk bitmap = (bitmap, testBit bitmap <$> fi)
