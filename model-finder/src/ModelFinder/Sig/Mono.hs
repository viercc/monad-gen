{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module ModelFinder.Sig.Mono where

import Control.Monad (guard)
import Data.Constraint.Extras (Has (has))
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.GADT.Compare
import Data.GADT.Show (GShow (..))
import Data.Map.Lazy (Map)
import Data.Map.Lazy qualified as Map
import Data.Set qualified as Set
import Data.Type.Equality (type (:~:) (..))
import ModelFinder.Solver (Def (..), Model (..), Solution (..))

data Sig args ret ret' where
  Sig :: args -> Sig args ret ret

sigToRefl :: Sig a r x -> r :~: x
sigToRefl Sig {} = Refl

deriving instance (Eq args) => Eq (Sig args ret ret')

deriving instance (Ord args) => Ord (Sig args ret ret')

deriving instance (Show args) => Show (Sig args ret ret')

instance (Eq args) => GEq (Sig args ret) where
  geq sa sb = case (sigToRefl sa, sigToRefl sb) of
    (Refl, Refl) -> guard (sa == sb) *> Just Refl

instance (Ord args) => GCompare (Sig args ret) where
  gcompare sa sb = case (sigToRefl sa, sigToRefl sb) of
    (Refl, Refl) -> genOrdering (compare sa sb)

instance (Show args) => GShow (Sig args ret) where
  gshowsPrec = showsPrec

genOrdering :: Ordering -> GOrdering t t
genOrdering cmp = case cmp of
  LT -> GLT
  EQ -> GEQ
  GT -> GGT

instance (c ret) => Has c (Sig args ret) where
  has sig body = case sigToRefl sig of Refl -> body

monoMakeModel :: (Ord args) => Map args (Set.Set ret) -> Model (Sig args ret)
monoMakeModel m = Model $ DMap.fromList [(Sig args :=> rs) | (args, rs) <- Map.toList m]

monoSolutionToMap :: (Ord args) => Solution (Sig args ret) -> Map args ret
monoSolutionToMap (Solution defs) = Map.fromList [(arg, ret) | Sig arg := ret <- defs]