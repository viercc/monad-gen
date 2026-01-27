{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
module ModelFinder.Solver(
  -- * Model finding entry point
  solve, solveEqs,
  Snapshot,
  preInitialize,
  solveFromSnapshot
) where

import Data.Function (on)
import Control.Applicative (Alternative(..))
import Control.Monad ( guard, MonadPlus (..) )
import Data.Maybe (isNothing, mapMaybe)
import Data.List (sortOn)
import Data.Ord (Down(..))
import Data.Traversable (for)
import LensUtil ( toListOf )
import qualified Data.Foldable as F

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Equality.Graph
import Data.Equality.Analysis.Monadic (AnalysisM (..))
import Data.Equality.Graph.Lens
import Data.Equality.Utils.SizedList (sizeSL)

import ModelFinder.Model
import ModelFinder.Term
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import ModelFinder.Solver.Internal
import ModelFinder.Term.EGraph (EGraph', equateDefs, equateTerms)

type DebugConstraint f a = (Show a, Show (f a), Show (f (Term f a)), Show (f Int))

-- * Analysis data and monadic environment for it

data ModelInfo k a = ModelInfo {
    constValue :: !(Maybe a),
    -- ^ The class contains (Con a)
    constFunctions :: !(Set k)
    -- ^ The class contains (Fun fx) where all of its children
    --   classes contain a constant value.
  }
  deriving (Show)

instance (Eq a) => Eq (ModelInfo k a) where
  (==) = (==) `on` constValue

instance (Ord a, Language f, Model (f a) a model)
    => AnalysisM (SearchM (f a) a model) (ModelInfo (f a) a) (L f a) where
  makeA :: L f a (ModelInfo (f a) a) -> SearchM (f a) a model (ModelInfo (f a) a)
  makeA (Con a) = pure $ ModelInfo (Just a) Set.empty
  makeA (Fun fd) = pure $ ModelInfo Nothing funSet
    where
      funSet = maybe Set.empty Set.singleton (traverse constValue fd)
  
  joinA :: ModelInfo (f a) a -> ModelInfo (f a) a -> SearchM (f a) a model (ModelInfo (f a) a)
  joinA d1 d2 = case (con1, con2) of
    (Nothing, Nothing) -> do
      let eqs = take 1 (Set.toList fun1) ++ take 1 (Set.toList fun2)
      enterEqsM eqs
      pure d'
    (Nothing, Just a2) -> do
      enterDefsM (Set.toList fun1) a2
      pure d'
    (Just a1, Nothing) -> do
      enterDefsM (Set.toList fun2) a1
      pure d'
    (Just a1, Just a2) -> do
      guard (a1 == a2)
      pure d'
    where
      ModelInfo con1 fun1 = d1
      ModelInfo con2 fun2 = d2
      d' = ModelInfo (con1 <|> con2) (Set.union fun1 fun2)

-- * Model search algorithm

solve :: (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => [a]
  -> [Property f]
  -> Map (f a) a
  -> model
  -> [model]
solve univ props = solveEqs eqs
  where
    eqs = props >>= runProperty univ

solveEqs :: (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> model
  -> [model]
solveEqs eqs knownDefs model0 = snd <$> runSearchM model0 body
  where
    body = initialize eqs knownDefs >>= solveBody

type Snapshot f a m = (EG f a, m)

preInitialize :: (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> model
  -> Maybe (Snapshot f a model)
preInitialize eqs knownDefs model0 = case runSearchM model0 (initialize eqs knownDefs) of
  [] -> Nothing
  [(eg, model)] -> Just (eg, model)
  (_:_:_) -> errorWithoutStackTrace "initialize doesn't branch out"

solveFromSnapshot :: (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> Snapshot f a model
  -> [model]
solveFromSnapshot eqs knownDefs (eg0, model0) = snd <$> runSearchM model0 body
  where
    body = initializeFrom eg0 eqs knownDefs >>= solveBody

-- Shorthand
type EG f a = EGraph' (ModelInfo (f a) a) f a

solveBody :: forall a f model.
     (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => EG f a
  -> SearchM (f a) a model ()
solveBody eg = case whatToGuess eg of
  [] -> pure ()
  (fas : _) -> guessFor eg fas >>= solveBody

guessFor :: forall a f model.
     (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => EG f a
  -> NonEmpty (f a)
  -> SearchM (f a) a model (EG f a)
guessFor eg fas = do
  m <- getsModel
  a <- choose (guessMany fas m)
  (m', newDefs) <- maybeToSearch $ enterDef (F.toList fas) a m
  putModel m'
  let updateDefs = (NE.head fas, a) : newDefs
  syncLoop eg updateDefs []

initialize :: (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> SearchM (f a) a model (EG f a)
initialize = initializeFrom emptyEGraph

initializeFrom :: (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => EG f a
  -> [(Term f a, Term f a)]
  -> Map (f a) a
  -> SearchM (f a) a model (EG f a)
initializeFrom eg0 eqs defs = do
  model0 <- getsModel
  (defs', model1) <- maybeToSearch $ saturateModel model0 (Map.toList defs)
  putModel model1
  eg1 <- syncLoop eg0 (Map.toList defs') eqs
  discoveries <- discoverDefs eg1
  syncLoop eg1 discoveries []

discoverDefs :: (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => EG f a
  -> SearchM (f a) a model [(f a, a)]
discoverDefs eg = do
  m <- getsModel
  defs <- for (getUnknownFunctionGroups eg) $ \ks ->
    case guessMany ks m of
      -- Empty result ==> early failure
      [] -> mzero
      -- Unique guess ==> discovered
      [a] -> pure [(NE.head ks, a)]
      -- Other ==> No discovery
      _ -> pure []
  pure $ concat defs

syncLoop :: forall f a model.
    (Ord a, Language f, Model (f a) a model)
  => DebugConstraint f a
  => EG f a -> [(f a,a)] -> [(Term f a, Term f a)] -> SearchM (f a) a model (EG f a)
syncLoop eg [] [] = pure eg
syncLoop eg defs eqs = do
  eg1 <- equateDefs defs eg
  eg2 <- equateTerms eqs eg1
  eg3 <- rebuildM eg2
  updates <- takeAllWaitingDefs
  syncLoop eg3 updates []

getUnknownFunctionGroups :: (Ord a, Language f) => EG f a -> [NonEmpty (f a)]
getUnknownFunctionGroups = mapMaybe getFunGroup . filter isUnknownValue . toListOf _classes
  where
    isUnknownValue cls = isNothing $ constValue (cls ^. _data)
    getFunGroup = NE.nonEmpty . Set.toList . constFunctions . view _data

whatToGuess :: (Ord a, Language f) => EG f a -> [NonEmpty (f a)]
whatToGuess = mapMaybe getFunGroup . sortOn (Down . getParentCount) . filter isUnknownValue . toListOf _classes
  where
    isUnknownValue cls = isNothing $ constValue (cls ^. _data)
    getParentCount cls = sizeSL (cls ^. _parents)
    getFunGroup = NE.nonEmpty . Set.toList . constFunctions . view _data
