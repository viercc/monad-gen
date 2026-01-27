{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
module ModelFinder.Solver.NFSolver(
  -- * Model finding entry point
  NormalForm(..),
  solveEqs,
  preInitialize, solveFromSnapshot,
) where

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
import ModelFinder.Term.EGraph (EGraph', equateDefs, equateTerms, representFun)
import Data.Bifunctor (Bifunctor(..))

type DebugConstraint f a = (Show a, Show (f a), Show (f (Term f a)), Show (f Int))

-- * Analysis data and monadic environment for it

data ModelInfo k a = ModelInfo {
    constValue :: !(Maybe a),
    -- ^ The class contains (Con a)
    constFunctionsClean :: !(Set k),
    -- ^ The class contains (Fun fx) where each children
    --   classes of fx contain constant value a.
    constFunctionsDirty :: !(Set k)
    -- ^ The class contains (Fun fx) where each children
    --   classes of fx contain constant value a.
  }
  deriving (Show)

constFunctions :: Ord k => ModelInfo k a -> Set k
constFunctions d = Set.union (constFunctionsClean d) (constFunctionsDirty d)

instance (Eq k, Eq a) => Eq (ModelInfo k a) where
  d1 == d2 =
    (constValue d1 == constValue d2) &&
      (constFunctionsDirty d1 == constFunctionsDirty d2)
    -- no need to compare constFunctionsClean

-- | normalize . reify === id
class NormalForm syn val | val -> syn where
  normalize :: syn -> val
  reify :: val -> syn

instance (Ord a, Ord k, Language f, NormalForm (f a) k, Model k a model)
    => AnalysisM (SearchM k a model) (ModelInfo k a) (L f a) where
  makeA :: L f a (ModelInfo k a) -> SearchM k a model (ModelInfo k a)
  makeA (Con a) = pure $ ModelInfo (Just a) Set.empty Set.empty
  makeA (Fun fd) = case traverse constValue fd of
    Nothing -> pure $ ModelInfo Nothing Set.empty Set.empty
    Just fa ->
      let k = normalize fa
          (clean, dirty)
            | fa == reify k = (Set.singleton k, Set.empty)
            | otherwise     = (Set.empty, Set.singleton k)
      in pure $ ModelInfo Nothing clean dirty
  
  joinA :: ModelInfo k a -> ModelInfo k a -> SearchM k a model (ModelInfo k a)
  joinA d1 d2 = case (con1, con2) of
    (Nothing, Nothing) -> do
      let eqs = take 1 (Set.toList cf1 <> Set.toList df1)
                ++ take 1 (Set.toList cf2 <> Set.toList df2)
      enterEqsM eqs
      pure $ ModelInfo Nothing cf' df'
    (Nothing, Just a2) -> do
      enterDefsM (Set.toList (cf1 <> df1)) a2
      pure $ ModelInfo (Just a2) cf' df'
    (Just a1, Nothing) -> do
      enterDefsM (Set.toList (cf2 <> df2)) a1
      pure $ ModelInfo (Just a1) cf' df'
    (Just a1, Just a2) -> do
      guard (a1 == a2)
      pure $ ModelInfo (Just a1) cf' df'
    where
      ModelInfo con1 cf1 df1 = d1
      ModelInfo con2 cf2 df2 = d2
      cf' = Set.union cf1 cf2
      df' = Set.union (df1 Set.\\ cf2) (df2 Set.\\ cf1)
    
  modifyA classId eg = do
    let classData = eg ^. _class classId . _data
        funs = Set.toList $ constFunctionsDirty classData
        terms = reify <$> funs
    loop eg classId terms
    where
      loop :: EG f a k -> ClassId -> [f a] -> SearchM k a model (EG f a k)
      loop eg0 _ [] = pure eg0
      loop eg0 c0 (t : rest) = do
        (c1, eg1) <- representFun t eg0
        (_, eg2) <- mergeM c0 c1 eg1
        loop eg2 c0 rest

-- * Model search algorithm

solveEqs :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map k a
  -> model
  -> [model]
solveEqs eqs knownDefs model0 = snd <$> runSearchM model0 body
  where
    body = initialize eqs knownDefs >>= solveBody

type Snapshot f a k m = (EG f a k, m)

preInitialize :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map k a
  -> model
  -> Maybe (Snapshot f a k model)
preInitialize eqs knownDefs model0 = case runSearchM model0 (initialize eqs knownDefs) of
  [] -> Nothing
  [(eg, model)] -> Just (eg, model)
  (_:_:_) -> errorWithoutStackTrace "initialize doesn't branch out"

solveFromSnapshot :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map k a
  -> Snapshot f a k model
  -> [model]
solveFromSnapshot eqs knownDefs (eg0, model0) = snd <$> runSearchM model0 body
  where
    body = initializeFrom eg0 eqs knownDefs >>= solveBody

-- Shorthand
type EG f a k = EGraph' (ModelInfo k a) f a

solveBody :: forall a f k model.
     (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => EG f a k
  -> SearchM k a model ()
solveBody eg = case whatToGuess eg of
  [] -> pure ()
  (fas : _) -> guessFor eg fas >>= solveBody

guessFor :: forall a f k model.
     (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => EG f a k
  -> NonEmpty k
  -> SearchM k a model (EG f a k)
guessFor eg fas = do
  m <- getsModel
  a <- choose (guessMany fas m)
  (m', newDefs) <- maybeToSearch $ enterDef (F.toList fas) a m
  putModel m'
  let updateDefs = (NE.head fas, a) : newDefs
  syncLoop eg updateDefs []

initialize :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map k a
  -> SearchM k a model (EG f a k)
initialize = initializeFrom emptyEGraph

initializeFrom :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => EG f a k
  -> [(Term f a, Term f a)]
  -> Map k a
  -> SearchM k a model (EG f a k)
initializeFrom eg0 eqs defs = do
  model0 <- getsModel
  (defs', model1) <- maybeToSearch $ saturateModel model0 (Map.toList defs)
  putModel model1
  eg1 <- syncLoop eg0 (Map.toList defs') eqs
  discoveries <- discoverDefs eg1
  syncLoop eg1 discoveries []

discoverDefs :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => EG f a k
  -> SearchM k a model [(k, a)]
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

syncLoop :: forall f a k model.
    (Ord a, Language f, Ord k, Model k a model, NormalForm (f a) k)
  => DebugConstraint f a
  => EG f a k -> [(k,a)] -> [(Term f a, Term f a)] -> SearchM k a model (EG f a k)
syncLoop eg [] [] = pure eg
syncLoop eg defs eqs = do
  eg1 <- equateDefs (first reify <$> defs) eg
  eg2 <- equateTerms eqs eg1
  eg3 <- rebuildM eg2
  updates <- takeAllWaitingDefs
  syncLoop eg3 updates []

getUnknownFunctionGroups :: (Ord a, Language f, Ord k) => EG f a k -> [NonEmpty k]
getUnknownFunctionGroups = mapMaybe getFunGroup . filter isUnknownValue . toListOf _classes
  where
    isUnknownValue cls = isNothing $ constValue (cls ^. _data)
    getFunGroup = NE.nonEmpty . Set.toList . constFunctions . view _data

whatToGuess :: (Ord a, Language f, Ord k) => EG f a k -> [NonEmpty k]
whatToGuess = mapMaybe getFunGroup . sortOn (Down . getParentCount) . filter isUnknownValue . toListOf _classes
  where
    isUnknownValue cls = isNothing $ constValue (cls ^. _data)
    getParentCount cls = sizeSL (cls ^. _parents)
    getFunGroup = NE.nonEmpty . Set.toList . constFunctions . view _data
