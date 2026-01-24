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

  -- * Languages
  L(..), Term,
  con, fun, liftFun,
  Property'(..), Property(..),
  runProperty
) where

import Data.Function (on, (&))
import Data.Bifunctor (Bifunctor(..))
import Control.Applicative (Alternative())
import Control.Monad ( guard, MonadPlus (..), when )
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
import Debug.Trace (traceM, trace)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Coerce (coerce)

type DebugConstraint f a = (Show a, Show (f a), Show (f (Term f a)), Show (f Int))

-- * Analysis data and monadic environment for it

data ModelInfo k a = ModelInfo {
    constValue :: !(Maybe a),
    -- ^ The class contains (Con a)
    constFunctions :: !(Set k),
    -- ^ The class contains (Fun fx) where each children
    --   classes of fx contain constant value a,
    --   and k = normalize fx.
    constFunctionsDone :: !(Set k)
    -- ^ If @normalize@ changes a @Fun fx@ term,
    --   i.e. @reify k /= fx@, the class
    --   may not contain @reify k@.
    --   Such a state must be temporary and corrected by @modifyA@.
  }
  deriving (Show, Eq)

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

enterEqsM :: Model k a model => [k] -> SearchM k a model ()
enterEqsM fas = do
  m <- getsModel
  (m', newDefs) <- maybeToSearch $ enterEqs fas m
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
    Just fa -> do
      let k = normalize fa
          doneSet
            | fa == reify k = Set.singleton k
            | otherwise = Set.empty
      pure $ ModelInfo Nothing (Set.singleton k) doneSet

  joinA :: ModelInfo k a -> ModelInfo k a -> SearchM k a model (ModelInfo k a)
  joinA d1 d2 = case (con1, con2) of
    (Nothing, Nothing) -> do
      let eqn = take 1 (Set.toList fun1) ++ take 1 (Set.toList fun2)
      enterEqsM eqn
      pure $ ModelInfo Nothing fun' df'
    (Nothing, Just a2) -> do
      enterDefsM (Set.toList fun1) a2
      pure $ ModelInfo (Just a2) fun' df'
    (Just a1, Nothing) -> do
      enterDefsM (Set.toList fun2) a1
      pure $ ModelInfo (Just a1) fun' df'
    (Just a1, Just a2) -> do
      guard (a1 == a2)
      pure $ ModelInfo (Just a1) fun' df'
    where
      ModelInfo con1 fun1 df1 = d1
      ModelInfo con2 fun2 df2 = d2
      fun' = Set.union fun1 fun2
      df' = Set.union df1 df2
    
  modifyA classId eg = do
    let classData = eg ^. _class classId . _data
        addedNFs = Set.difference (constFunctions classData) (constFunctionsDone classData)
    loop eg classId (Set.toList addedNFs)
    where
      loop :: EG f a k -> ClassId -> [k] -> SearchM k a model (EG f a k)
      loop eg0 _ [] = pure eg0
      loop eg0 c0 (k : rest) = do
        (c1, eg1) <- representM (liftFun (reify k)) eg0
        (c2, eg2) <- mergeM c0 c1 eg1
        loop eg2 c2 rest

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
solveEqs' eqs knownDefs model0 = snd <$> runSearchM model0 (solveBody eqs knownDefs)

-- Shorthand
type EG f a k = EGraph (ModelInfo k a) (L f a)

solveBody :: forall a f k model.
     (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map k a
  -> SearchM k a model ()
solveBody eqs knownDefs = do
  traceM "=== begin solveBody ==="
  F.for_ (Map.toList knownDefs) $ \(k,a) ->
    traceM $ "  |" ++ show (reify k) ++ " => " ++ show a
  traceM "= initialize ="
  eg1 <- initialize eqs knownDefs
  traceM "= loop ="
  loop eg1
  where
    loop :: EG f a k -> SearchM k a model ()
    loop eg = check >> case whatToGuess eg of
      [] -> pure ()
      (fas : _) -> guessFor eg fas >>= loop
      where
        check = checkEGraphValidity eg

checkEGraphValidity :: forall a f k model.
     (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => EG f a k -> SearchM k a model ()
checkEGraphValidity eg = mapM_ checkClass allClasses
  where
    allClasses = toListOf _iclasses eg
    checkClass (cid, cls) = do
      sameClassToNormalForm cid (cls ^. _nodes)
      matchWithModel (cls ^. _data)
    sameClassToNormalForm cid = mapM_ (validNode cid)
    validNode cls node = case node of
      Node (Con _) -> pure ()
      Node (Fun fx) -> case traverse getCon fx of
        Nothing -> pure ()
        Just fa -> do
          let nf = reify (normalize fa :: k)
          (nfId, eg') <- representM (liftFun nf) eg
          if nfId == cls
            then pure ()
            else do () <- dumpEGraph eg'
                    error $ "validNode: " ++ show (cls, fa, nfId, nf)
    getCon cid = constValue $ eg ^. _class cid . _data
    matchWithModel (ModelInfo cons funs _df) = case cons of
      Nothing -> pure ()
      Just a -> do
        m <- getsModel
        F.for_ funs $ \k -> case guess k m of
          [a'] | a == a' -> pure ()
          as -> error $ "matchWithModel: " ++ show (reify k, a, as)

guessFor :: forall a f k model.
     (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => EG f a k
  -> NonEmpty k
  -> SearchM k a model (EG f a k)
guessFor eg fas = do
  m <- getsModel
  let as = guessMany fas m
  a <- case as of
    [a] -> do
      traceM $ "  found " ++ show (reify <$> fas) ++ " => " ++ show a
      pure a
    _ -> do
      traceM $ "guessing: " ++ show (reify <$> fas)
      a <- choose as
      traceM $ "  guessed " ++ show (reify <$> fas) ++ " => " ++ show a
      pure a
  (m', newDefs) <- maybeToSearch $ enterDef (F.toList fas) a m
  putModel m'
  let updateDefs = (NE.head fas, a) : newDefs
  syncLoop eg (defToEq <$> updateDefs)

initialize :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => DebugConstraint f a
  => [(Term f a, Term f a)]
  -> Map k a
  -> SearchM k a model (EG f a k)
initialize eqs defs = do
  model0 <- getsModel
  (defs', model1) <- maybeToSearch $ saturateModel model0 (Map.toList defs)
  putModel model1
  eg <- syncLoop emptyEGraph ((defToEq <$> Map.toList defs') ++ eqs)
  dumpEGraph eg
  pure eg

dumpEGraph :: (Ord a, Language f, Ord k, NormalForm (f a) k, Monad m)
  => DebugConstraint f a
  => EG f a k
  -> m ()
dumpEGraph eg = do
  traceM "-- EGraph Debug dump --"
  F.for_ (toListOf _iclasses eg) $ \(i, clsData) -> do
    traceM $ "class " ++ show i ++ " {"
    dumpClassData (clsData ^. _data)
    F.for_ (clsData ^. _nodes) $ \node -> do
      traceM $ "  | " ++ show (unNode node)
    traceM $ "} end " ++ show i
    pure ()

dumpClassData :: (Ord a, Language f, Ord k, NormalForm (f a) k, Monad m)
  => DebugConstraint f a
  => ModelInfo k a
  -> m ()
dumpClassData (ModelInfo cons funs df) = do
  traceM "  ModelInfo {"
  traceM $ "  cons = " ++ show cons
  traceM $ "  funs = " ++ showSetKey funs
  traceM $ "  df   = " ++ showSetKey df
  traceM "  }"
  where showSetKey ks = show (reify <$> Set.toList ks) ++ " (size=" ++ show (Set.size ks) ++ ")"

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
  => EG f a k -> [(Term f a, Term f a)] -> SearchM k a model (EG f a k)
syncLoop eg [] = pure eg
syncLoop eg eqs = do
  eg1 <- equateTerms eqs eg
  eg2 <- rebuildM eg1

  -- updates from model
  updates <- takeAllWaitingDefs
  let updateEqs = defToEq <$> updates

  syncLoop eg2 updateEqs

whatToGuess :: (Ord a, Language f) => EG f a k -> [NonEmpty k]
whatToGuess = mapMaybe getFunGroup . sortOn (Down . getParentCount) . filter isUnknownValue . toListOf _classes
  where
    isUnknownValue cls = isNothing $ constValue (cls ^. _data)
    getParentCount cls = sizeSL (cls ^. _parents)
    getFunGroup = NE.nonEmpty . Set.toList . constFunctions . view _data

defToEq :: (Functor f, NormalForm (f a) k) => (k, a) -> (Term f a, Term f a)
defToEq = bimap (liftFun . reify) con

equateDefs :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => [(k, a)] -> EG f a k -> SearchM k a model (EG f a k)
equateDefs defs = equateTerms (defToEq <$> defs)

equate :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => Term f a -> Term f a -> EG f a k -> SearchM k a model (EG f a k)
equate lhs rhs eg = do
  (cLhs, eg1) <- representM lhs eg
  (cRhs, eg2) <- representM rhs eg1
  (_, eg3) <- mergeM cLhs cRhs eg2
  pure eg3

equateTerms :: (Ord a, Language f, Ord k, NormalForm (f a) k, Model k a model)
  => [(Term f a, Term f a)] -> EG f a k -> SearchM k a model (EG f a k)
equateTerms [] eg = pure eg
equateTerms ((lhs, rhs) : rest) eg = equate lhs rhs eg >>= equateTerms rest

----

transposeMap :: (Ord a, Ord b) => Map a b -> Map b (Set a)
transposeMap m = Map.fromListWith Set.union
  [ (b, Set.singleton a) | (a, b) <- Map.toList m ]

-- Map.fromList but the values for the repeated keys must be unique
mapFromListUnique :: (Ord k, Eq v) => [(k,v)] -> Maybe (Map k v)
mapFromListUnique = F.foldlM step Map.empty
  where
    step m (k,v) = Map.alterF (checkedInsert v) k m
    checkedInsert newV old = case old of
      Nothing -> Just (Just newV)
      Just oldV -> old <$ guard (newV == oldV)

----

type LensLike f s t a b = (a -> f b) -> s -> f t

foldMapOf :: LensLike (Const m) s t a b -> (a -> m) -> s -> m
foldMapOf trav f = getConst . trav (Const . f)

toListOf :: LensLike (Const (Endo [a])) s t a b -> s -> [a]
toListOf trav = concretize . foldMapOf trav (\a -> Endo (a:))
  where
    concretize endo = appEndo endo []
