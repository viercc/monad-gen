{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
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

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import qualified Data.Foldable as F
import Data.Bool (bool)
import Data.Bits
import Data.Maybe (mapMaybe)

import qualified Data.PreNatMap as PNM
import Data.PreNatMap (PreNatMap)

import Data.FunctorShape
import ModelFinder.Model ( Model(..) )
import ModelFinder.Term
import ModelFinder.Solver ( solveEqs )

import Data.PTraversable.Extra (_indices, _zipMatchWith, shapes, skolem)

import qualified Data.BoolSet as BoolSet
import GHC.Generics ((:.:) (..))
import ApplicativeGen (ApplicativeDict(..))
import Data.PTraversable (PTraversable, enum1)

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

fromJ :: J (f Bool) -> BinaryJoin f Bool
fromJ (J x y0 y1) = BJ x y0 y1

-- * Model for BinaryJoin

data BinaryJoinModel f = BinaryJoinModel
  {
    allShapes :: Set (Shape f),
    joinPreNatMap :: PreNatMap (BinaryJoin f) f
  }

deriving instance (forall x. Show x => Show (f x), Traversable f) => Show (BinaryJoinModel f)

instance (Traversable f, (forall a. Ord a => Ord (f a))) => Model J (f Bool) (BinaryJoinModel f) where
  guess query m = case PNM.lookup ff (joinPreNatMap m) of
      Nothing -> [ fa | Shape f <- Set.toList (allShapes m), fa <- traverse (const content) f ]
      Just fa -> traverse BoolSet.toList fa
    where
      ff = BoolSet.singleton <$> fromJ query
      content = BoolSet.toList . BoolSet.unions $ F.toList ff
  
  enterDef js rhs m = do
    let pnm = joinPreNatMap m
    (pnm', newFullShapes) <- loop pnm Set.empty js
    let newDefs = do
          Shape ff <- Set.toList newFullShapes
          let lhsInt = _indices ff
          rhsInt <- toList $ PNM.fullMatch lhsInt pnm'
          pure (Shape lhsInt, rhsInt)
    pure (m{ joinPreNatMap = pnm' }, newDefs >>= makeBinaryJoinDefs)
    where
      loop pnm newFull [] = pure (pnm, newFull)
      loop pnm newFull (query : rest) = case PNM.match ff pnm of
        -- Do nothing for known result
        Just y -> guard (rhs == y) *> loop pnm newFull rest
        -- Refine for unknown result
        Nothing -> do
          pnm' <- PNM.refine ff rhs pnm
          let -- If the refine made a "fully known" shape, record it
              newFull'
                | PNM.isFull (Shape ff) pnm' = Set.insert (Shape ff) newFull
                | otherwise = newFull
          loop pnm' newFull' rest
        where
          ff = fromJ query

  enterEqs ::
    [J (f Bool)]
    -> BinaryJoinModel f
    -> Maybe (BinaryJoinModel f, [(J (f Bool), f Bool)])
  enterEqs js m = case guesses of
    -- No guess is made for js
    [] -> Just (m, [])
    (guess0 : guesses') -> do
        -- Try to unify all guesses
        commonGuess <- unifyAllGuesses guess0 guesses'
        case traverse BoolSet.uniqueBool commonGuess of
          Nothing -> Just (m, [])
          -- if the guess determines a unique answer,
          -- 'enterDef'.
          Just rhs -> enterDef js rhs m
    where
      guessMaybe query = PNM.lookup (BoolSet.singleton <$> fromJ query) (joinPreNatMap m)
      guesses = mapMaybe guessMaybe js
      unifyAllGuesses g [] = pure g
      unifyAllGuesses g (g' : rest) = do
        g'' <- _zipMatchWith (\x y -> nonEmptyAmb $ BoolSet.intersection x y) g g'
        unifyAllGuesses g'' rest
      nonEmptyAmb x = x <$ guard (x /= BoolSet.empty)

makeBinaryJoinDefs :: Traversable f => (Shape (BinaryJoin f), f Int) -> [(J (f Bool), f Bool)]
makeBinaryJoinDefs (Shape bj, rhs) =
  do (bitmap, BJ x y0 y1) <- boolTable bj
     let rhsBool = testBit bitmap <$> rhs
     pure (J x y0 y1, rhsBool)

-- * Generation logic

genFromPure :: forall f. PTraversable f => Shape f -> [PreNatMap (BinaryJoin f) f]
genFromPure pureShape = joinPreNatMap <$> solveEqs allEqs allDefs model0
  where
    fShapes = Shape <$> shapes
    model0 = BinaryJoinModel { allShapes = Set.fromList fShapes, joinPreNatMap = PNM.empty }
    allEqs = constEqs ++ notEqs ++ assocEqs
    allDefs = Map.unions [unitLeftDefs pureShape, unitRightDefs pureShape, zeroDefs]

gen :: forall f. (PTraversable f) => [PreNatMap (BinaryJoin f) f]
gen = shapes >>= genFromPure . Shape

genFromApplicative :: forall f. (PTraversable f) => ApplicativeDict f -> [PreNatMap (BinaryJoin f) f]
genFromApplicative apDict = joinPreNatMap <$> solveEqs allEqs allDefs model0
  where
    fShapes = Shape <$> shapes
    model0 = BinaryJoinModel { allShapes = Set.fromList fShapes, joinPreNatMap = PNM.empty }
    allEqs = constEqs ++ notEqs ++ assocEqs
    allDefs = Map.unions [apDefs apDict, zeroDefs]

binaryJoinToJoin :: (Traversable f, (forall a. Ord a => Ord (f a))) => PreNatMap (BinaryJoin f) f -> PreNatMap (f :.: f) f
binaryJoinToJoin binaryJoinData = PNM.make (buildEntry <$> PNM.toEntries binaryJoinData)
  where
    buildEntry (PNM.PreEntry (BJ x y0 y1) rhs) = PNM.PreEntry (Comp1 (bool y0 y1 <$> x)) rhs

-- Utilities

type Bitmap = Word

boolTable :: Traversable f => f any -> [(Bitmap, f Bool)]
boolTable f
  | n <= lenMax = mk <$> [0 .. 2 ^ n - 1]
  | otherwise = error $ "too long: " ++ show n ++ " >= " ++ show lenMax
  where
    lenMax = finiteBitSize (0 :: Word) `div` 2
    n = length f
    fi = _indices f
    mk bitmap = (bitmap, testBit bitmap <$> fi)
