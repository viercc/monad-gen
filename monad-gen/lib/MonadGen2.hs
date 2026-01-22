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

module MonadGen2
  (
    module MonadData,

    genFromApplicative,
    moduloIso,
    genFromApplicativeModuloIso,
    genFromApplicativeIsoGroups,
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
import Data.Bifunctor (Bifunctor(..))
import Debug.Trace (traceM)

import MonadData
import ModelFinder.Model.PreNatMapModel
import ModelFinder.Model
import ModelFinder.Term
import ModelFinder.Solver (solveEqs)

import GHC.Generics ((:.:) (..))
import Data.Finitary.Enum (enum)

-- Generation

-- |
--
-- >>> apDict = ApplicativeDict Just liftA2
-- >>> length $ genFromApplicative apDict
-- 1

genFromApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicative apDict = do
  apDefs <- F.toList $ applicativeDefs apDict
  let def0 = Map.fromList $ map (first (Join . unComp1)) $ PNM.toEntries apDefs
  -- traceM $ "def0.size = " ++ show (Map.size def0)
  model <- solveEqs associativityEqs def0 newJoinModel
  pure $ postprocess model
  where
    pureShape = Shape (_applicativePure apDict ())

    postprocess :: JoinModel f -> MonadData f
    postprocess (JoinModel (PreNatMapModel _ pnm)) = MonadData pureShape (PNM.toNatMap pnm)

moduloIso :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f] -> [MonadData f]
moduloIso apDict = uniqueByIso isoGenerators
  where
    isoGenerators = stabilizingIsomorphisms apDict

genFromApplicativeModuloIso :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicativeModuloIso apDict = moduloIso apDict $ genFromApplicative apDict

genFromApplicativeIsoGroups :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [Set.Set (MonadData f)]
genFromApplicativeIsoGroups apDict = groupByIso isoGenerators $ genFromApplicative apDict
  where
    isoGenerators = stabilizingIsomorphisms apDict

-- Model

data LHS f k r =
    Join (f r)
  | Bind (V.Vector k) r
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

newtype JoinModel f = JoinModel (PreNatMapModel (f :.: f) f)

toComp :: Functor f => LHS f (f Int) (f Int) -> (f :.: f) Int
toComp (Join ffr) = Comp1 ffr
toComp (Bind fxs fi) = Comp1 $ (fxs V.!) <$> fi

isBind :: LHS f k r -> Bool
isBind Join{} = False
isBind Bind{} = True

newJoinModel :: PTraversable f => JoinModel f
newJoinModel = JoinModel $ PreNatMapModel {
    allShapes = Set.fromList enum,
    pnmGuesses = PNM.empty
  }

instance (Traversable f, forall a. Ord a => Ord (f a)) => Model (LHS f (f Int) (f Int)) (f Int) (JoinModel f) where
  guess lhs (JoinModel impl) = guess (toComp lhs) impl

  enterDef lhss rhs (JoinModel impl) = bimap JoinModel modifyDefs <$> enterDef lhss' rhs impl
    where
      lhss' = toComp <$> lhss
      newLhss = map toComp $ filter isBind lhss
      modifyDefs defs = map (first (Join . unComp1)) $ ((, rhs) <$> newLhss) ++ defs

  enterEqs lhss (JoinModel impl) = bimap JoinModel modifyDefs <$> enterEqs lhss' impl
    where
      lhss' = toComp <$> lhss
      modifyDefs = map (first (Join . unComp1))

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
associativityEqs = (makeAssociativity .) <$> [outerIx, innerIx, allIx] <*> enum1 (enum1 shapes)

outerIx, innerIx, allIx :: Traversable f => f (f (f any)) -> f (f (f Int))
outerIx = imap (\i -> fmap (i <$))
innerIx = fmap (unComp1 . indices . Comp1)
allIx = unComp1 . unComp1 . indices . Comp1 . Comp1

applicativeDefs :: (PTraversable f) => ApplicativeDict f -> Maybe (PNM.PreNatMap (f :.: f) f)
applicativeDefs apDict = PNM.fromEntries $ do
  fi <- f1
  fj <- f1
  let lhs = Comp1 $ fmap (\i -> (i,) <$> fj) fi
      rhs = _applicativeLiftA2 apDict (,) fi fj
  pure (lhs, rhs)
  where
    f1 = V.toList skolem

separateFunctor :: (Traversable g, Ord a) => g a -> (V.Vector a, g Int)
separateFunctor ga = (V.fromList (F.toList ga), indices ga)
