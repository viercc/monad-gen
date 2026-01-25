{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE BangPatterns #-}
module ModelFinder.Solver(
  -- * Model finding entry point
  solve, solveEqs,

  -- ** Custom normalization
  solveEqs',
  NormalForm(..),

  preInitialize, solveFromSnapshot,

  -- * Languages
  L(..), Term,
  con, fun, liftFun,
  Property'(..), Property(..),
  runProperty
) where

import Data.Bifunctor (Bifunctor(..))
import Control.Applicative (Alternative())
import Control.Monad ( guard, MonadPlus (..) )
import Data.Maybe (isNothing, mapMaybe)
import Data.List (sortOn)
import Data.Ord (Down(..))
import Data.Functor.Const (Const(..))
import Data.Monoid (Endo(..))
import qualified Data.Foldable as F

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.State.Strict (StateT (..), MonadTrans (..))
import qualified Control.Monad.State.Class as State

import Data.Equality.Graph
import Data.Equality.Analysis.Monadic (AnalysisM (..))
import Data.Equality.Graph.Lens
import Data.Equality.Utils.SizedList (sizeSL)

import ModelFinder.Model
import ModelFinder.Term
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Coerce (coerce)
import Data.Traversable (for, mapAccumM)
import Data.Tuple (swap)

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

data SearchState k a model = SearchState {
    currentModel :: model,
    waitingDefs :: [(k, a)]
  }

-- | normalize . reify === id
class NormalForm syn val | val -> syn where
  normalize :: syn -> val
  reify :: val -> syn

newtype AsIs f a = AsIs (f a)
  deriving newtype (Show, Eq, Ord)
-- NOTICE: newtype-derived Show is intentional
-- (it is only for debug)

instance NormalForm (f a) (AsIs f a) where
  normalize = coerce
  reify = coerce

newtype SearchM k a model x = SearchM{ unSearchM :: StateT (SearchState k a model) [] x }
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)

runSearchM :: model -> SearchM k a model x -> [(x, model)]
runSearchM m0 mx = second currentModel <$> runStateT (unSearchM mx) (SearchState m0 [])

choose :: [a] -> SearchM k a model a
choose = SearchM . lift

maybeToSearch :: Maybe x -> SearchM k a model x
maybeToSearch = maybe mzero pure

enterDefsM :: Model k a model => [k] -> a -> SearchM k a model ()
enterDefsM fas a = do
  m <- getsModel
  (m', newDefs) <- maybeToSearch $ enterDef fas a m
  putModel m'
  pushWaitingDefs newDefs

getsModel :: SearchM k a model model
getsModel = SearchM $ State.gets currentModel

putModel :: model -> SearchM k a model ()
putModel m = SearchM $ State.modify $ \ss -> ss{ currentModel = m }

pushWaitingDefs :: [(k, a)] -> SearchM k a model ()
pushWaitingDefs newDefs = SearchM $ State.modify $ \ss ->
  ss{ waitingDefs = newDefs ++ waitingDefs ss }

-- Gets all waitingDefs and remove them from the state
takeAllWaitingDefs :: SearchM k a model [(k, a)]
takeAllWaitingDefs = SearchM $ State.state $ \ss ->
  (waitingDefs ss, ss{ waitingDefs = [] })

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
        terms = liftFun . reify <$> funs
    loop eg classId terms
    where
      loop :: EG f a k -> ClassId -> [Term f a] -> SearchM k a model (EG f a k)
      loop eg0 _ [] = pure eg0
      loop eg0 c0 (t : rest) = do
        (c1, eg1) <- representM t eg0
        (_, eg2) <- mergeM c0 c1 eg1
        loop eg2 c0 rest

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
solveEqs eqs knownDefs model0 =
  unwrapModel <$> solveEqs' eqs (Map.mapKeysMonotonic AsIs knownDefs) (WrapperModel model0)

solveEqs' :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map k a
  -> model
  -> [model]
solveEqs' eqs knownDefs model0 = snd <$> runSearchM model0 body
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
type EG f a k = EGraph (ModelInfo k a) (L f a)

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

saturateModel :: (Ord a, Ord k, Model k a model)
  => model -> [(k, a)] -> Maybe (Map k a, model)
saturateModel m0 = loop m0 Map.empty
  where    
    loop m !acc [] = pure (acc, m)
    loop m !acc ((k, a) : rest) = do
      (m', newDefs) <- enterDef [k] a m
      loop m' (Map.insert k a acc) (newDefs ++ rest)

syncLoop :: forall f a k model.
    (Ord a, Language f, Ord k, Model k a model, NormalForm (f a) k)
  => DebugConstraint f a
  => EG f a k -> [(k,a)] -> [(Term f a, Term f a)] -> SearchM k a model (EG f a k)
syncLoop eg [] [] = pure eg
syncLoop eg defs eqs = do
  eg1 <- equateDefs defs eg
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

representCon :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => a -> EG f a k -> SearchM k a model (ClassId, EG f a k)
representCon a = addM (Node (Con a))

representFun :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => f a -> EG f a k -> SearchM k a model (ClassId, EG f a k)
representFun fa eg0 = do
  (eg1, fx) <- mapAccumM (\eg a -> swap <$> representCon a eg) eg0 fa
  addM (Node (Fun fx)) eg1

equate :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => (Term f a, Term f a) -> EG f a k -> SearchM k a model (EG f a k)
equate (lhs, rhs) eg = do
  (cLhs, eg1) <- representM lhs eg
  (cRhs, eg2) <- representM rhs eg1
  (_, eg3) <- mergeM cLhs cRhs eg2
  pure eg3

equateDef :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => (k, a) -> EG f a k -> SearchM k a model (EG f a k)
equateDef (k, a) eg = do
  (cLhs, eg1) <- representFun (reify k) eg
  (cRhs, eg2) <- representCon a eg1
  (_, eg3) <- mergeM cLhs cRhs eg2
  pure eg3

equateTerms :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => [(Term f a, Term f a)] -> EG f a k -> SearchM k a model (EG f a k)
equateTerms [] eg = pure eg
equateTerms (eq : rest) eg = equate eq eg >>= equateTerms rest

equateDefs :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => [(k, a)] -> EG f a k -> SearchM k a model (EG f a k)
equateDefs [] eg = pure eg
equateDefs (eq : rest) eg = equateDef eq eg >>= equateDefs rest

----

type LensLike f s t a b = (a -> f b) -> s -> f t

foldMapOf :: LensLike (Const m) s t a b -> (a -> m) -> s -> m
foldMapOf trav f = getConst . trav (Const . f)

toListOf :: LensLike (Const (Endo [a])) s t a b -> s -> [a]
toListOf trav = concretize . foldMapOf trav (\a -> Endo (a:))
  where
    concretize endo = appEndo endo []
