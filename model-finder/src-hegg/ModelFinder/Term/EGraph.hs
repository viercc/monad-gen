{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
-- | Functions handling 'EGraph' on 'Term's.
module ModelFinder.Term.EGraph where

import Data.Tuple (swap)
import Data.Traversable (mapAccumM)

import Data.Equality.Graph
import Data.Equality.Analysis.Monadic
import ModelFinder.Term

type EGraph' d f a = EGraph d (L f a)

representCon :: (Ord a, Language f, AnalysisM m d (L f a))
  => a -> EGraph' d f a -> m (ClassId, EGraph' d f a)
representCon a = addM (Node (Con a))

representFun :: (Ord a, Language f, AnalysisM m d (L f a))
  => f a -> EGraph' d f a -> m (ClassId, EGraph' d f a)
representFun fa eg0 = do
  (eg1, fx) <- mapAccumM (\eg a -> swap <$> representCon a eg) eg0 fa
  addM (Node (Fun fx)) eg1

equate :: (Ord a, Language f, AnalysisM m d (L f a))
  => (Term f a, Term f a) -> EGraph' d f a -> m (EGraph' d f a)
equate (lhs, rhs) eg = do
  (cLhs, eg1) <- representM lhs eg
  (cRhs, eg2) <- representM rhs eg1
  (_, eg3) <- mergeM cLhs cRhs eg2
  pure eg3

equateDef :: (Ord a, Language f, AnalysisM m d (L f a))
  => (f a, a) -> EGraph' d f a -> m (EGraph' d f a)
equateDef (k, a) eg = do
  (cLhs, eg1) <- representFun k eg
  (cRhs, eg2) <- representCon a eg1
  (_, eg3) <- mergeM cLhs cRhs eg2
  pure eg3

equateTerms :: (Ord a, Language f, AnalysisM m d (L f a))
  => [(Term f a, Term f a)] -> EGraph' d f a -> m (EGraph' d f a)
equateTerms [] eg = pure eg
equateTerms (eq : rest) eg = equate eq eg >>= equateTerms rest

equateDefs :: (Ord a, Language f, Ord (f a), AnalysisM m d (L f a))
  => [(f a, a)] -> EGraph' d f a -> m (EGraph' d f a)
equateDefs [] eg = pure eg
equateDefs (eq : rest) eg = equateDef eq eg >>= equateDefs rest
