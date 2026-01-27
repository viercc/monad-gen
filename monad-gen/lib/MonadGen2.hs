{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}

module MonadGen2
  (
    module MonadData,

    prepareGenFromApplicative,
    genFromApplicative,
    moduloIso,
    groupsIso
  )
where

import qualified Data.Foldable as F
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set

import Data.PTraversable
import Data.PTraversable.Extra
import Data.Traversable.Extra (indices, imap)
import Data.FunctorShape

import ApplicativeGen

import qualified Data.Vector as V
import qualified Data.PreNatMap as PNM

import MonadData
import ModelFinder.Model.PreNatMapModel
import ModelFinder.Term
import ModelFinder.Solver.NFSolver

import GHC.Generics ((:.:) (..))
import Data.Finitary.Enum (enum)
import Data.Coerce (coerce, Coercible)
import qualified Data.NatMap as NM
import Control.Monad (guard)

-- Generation

prepareGenFromApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Maybe (ApplicativeDict f -> [MonadData f])
prepareGenFromApplicative = do
  snapshot <- preInitialize associativityEqs Map.empty newJoinModel
  pure $ \apDict -> do
    apDefs <- F.toList $ applicativeDefs apDict
    let def0 = Map.fromList $ PNM.toEntries apDefs
    model <- solveFromSnapshot [] def0 snapshot
    pure $ postprocess apDict model

genFromApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicative apDict = do
  apDefs <- F.toList $ applicativeDefs apDict
  let def0 = Map.fromList $ PNM.toEntries apDefs
  -- traceM $ "def0.size = " ++ show (Map.size def0)
  eqs <- F.toList $ associativityEqsReduced apDefs
  model <- solveEqs eqs def0 newJoinModel
  pure $ postprocess apDict model

postprocess :: (PTraversable f) => ApplicativeDict f -> JoinModel f -> MonadData f
postprocess apDict (PreNatMapModel _ pnm) = MonadData pureShape joinMap
  where
    pureShape = Shape (_applicativePure apDict ())
    joinMap = coerceNatMapKeys (PNM.toNatMap pnm)

coerceNatMapKeys :: (forall a. Coercible (f a) (f' a), WeakOrd f') => NM.NatMap f g -> NM.NatMap f' g
coerceNatMapKeys nm = NM.fromEntries (NM.bimapEntry (mapShape coerce) id <$> NM.toEntries nm)

moduloIso :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f] -> [MonadData f]
moduloIso apDict = uniqueByIso isoGenerators
  where
    isoGenerators = stabilizingIsomorphisms apDict

groupsIso :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f] -> [Set.Set (MonadData f)]
groupsIso apDict = groupByIso isoGenerators
  where
    isoGenerators = stabilizingIsomorphisms apDict

-- Model

data LHS f k r =
    Join (f r)
  | Bind (V.Vector k) r
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

newtype J f x = J (f (f x))
  deriving (Functor, Foldable, Traversable)

deriving instance Show (f (f x)) => Show (J f x)
deriving instance Eq (f (f x)) => Eq (J f x)
deriving instance Ord (f (f x)) => Ord (J f x)

instance Functor f => NormalForm (LHS f (f Int) (f Int)) (J f Int) where
  normalize = toComp
  reify = Join . coerce

type JoinModel f = PreNatMapModel (J f) f

toComp :: Functor f => LHS f (f Int) (f Int) -> J f Int
toComp (Join ffr) = J ffr
toComp (Bind fxs fi) = J $ (fxs V.!) <$> fi

newJoinModel :: PTraversable f => JoinModel f
newJoinModel = PreNatMapModel {
    allShapes = Set.fromList enum,
    pnmGuesses = PNM.empty
  }

-- * Equations

type JTerm f = Term (LHS f (f Int)) (f Int)

rightAssocTerm :: Functor f => f (f (f Int)) -> JTerm f
rightAssocTerm = fun . Join . fmap (fun . Join . fmap con)

leftAssocTerm :: (Traversable f, Ord (f Int)) => f (f (f Int)) -> JTerm f
leftAssocTerm fffi = case separateFunctor (Comp1 fffi) of
  (vec, Comp1 ffj) -> fun $ Bind vec (fun . Join . fmap con $ ffj)

makeAssociativity :: (Traversable f, Ord (f Int)) => f (f (f Int)) -> (JTerm f, JTerm f)
makeAssociativity f3 = (leftAssocTerm f3, rightAssocTerm f3)

-- associativityEqs :: (PTraversable f) => [(JTerm f, JTerm f)]
-- associativityEqs = makeAssociativity <$> V.toList skolem3

associativityEqs :: (PTraversable f) => [(JTerm f, JTerm f)]
associativityEqs = (makeAssociativity .) <$> [outerIx, innerIx] <*> enum1 (enum1 shapes)

associativityEqsReduced :: (PTraversable f) => PNM.PreNatMap (J f) f -> Maybe [(JTerm f, JTerm f)]
associativityEqsReduced pnm = concat <$> traverse checkAndRemove associativityEqs
  where
    red = reduceJTerm pnm
    checkAndRemove (lhs, rhs) = case (red lhs, red rhs) of
      (Fix (Con lhsCon), Fix (Con rhsCon)) -> [] <$ guard (lhsCon == rhsCon)
      (lhs', rhs') -> Just [(lhs', rhs')]

outerIx, innerIx :: Traversable f => f (f (f any)) -> f (f (f Int))
outerIx = imap (\i -> fmap (i <$))
innerIx = fmap (unComp1 . indices . Comp1)

applicativeDefs :: (PTraversable f) => ApplicativeDict f -> Maybe (PNM.PreNatMap (J f) f)
applicativeDefs apDict = PNM.fromEntries $ do
  fi <- f1
  fj <- f1
  let lhs = J $ fmap (\i -> (i,) <$> fj) fi
      rhs = _applicativeLiftA2 apDict (,) fi fj
  pure (lhs, rhs)
  where
    f1 = V.toList skolem

reduceJTerm :: forall f. (PTraversable f) => PNM.PreNatMap (J f) f -> JTerm f -> JTerm f
reduceJTerm pnm = go
  where
    tryReduceJ (J ffx) = case PNM.match (J ffx) pnm of
      Nothing -> fun (Join (con <$> ffx))
      Just fx -> con fx
    
    getCon :: JTerm f -> Maybe (f Int)
    getCon (Fix (Con fi)) = Just fi
    getCon _ = Nothing

    go :: JTerm f -> JTerm f
    go (Fix lt) = case go <$> lt of
      Con fi -> con fi
      Fun (Bind vec r) -> case getCon r of
        Just fi -> tryReduceJ $ J ((vec V.!) <$> fi)
        Nothing -> fun (Bind vec r)
      Fun (Join fr) -> case traverse getCon fr of
        Just ffi -> tryReduceJ $ J ffi
        Nothing -> fun (Join fr)

separateFunctor :: (Traversable g, Ord a) => g a -> (V.Vector a, g Int)
separateFunctor ga = (V.fromList (F.toList ga), indices ga)
