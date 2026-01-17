{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ModelFinder.Solver(
  -- * Model finding entry point
  solve, solveEqs,

  -- * Languages
  L(..), Term,
  con, fun, liftFun,
  Property'(..), Property(..),
  runProperty
) where

import Data.Function (on)
import Data.Bifunctor (Bifunctor(..))
import Control.Applicative (Alternative())
import Control.Monad ( guard, MonadPlus (..) )
import Data.Maybe (isNothing)
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

-- * Analysis data and monadic environment for it

data ModelInfo f a = ModelInfo {
    constValue :: !(Maybe a),
    -- ^ The class contains (Con a)
    constFunctions :: !(Set (f a))
    -- ^ The class contains (Fun fx) where each children
    --   classes of fx contain constant value a
  }
  deriving (Show)

-- | This is a BAD hack! Changes of @constFunctions@
--   do not need to trigger repair of parents.
instance Eq a => Eq (ModelInfo f a) where
  (==) = (==) `on` constValue

-- | This is a BAD hack! See @Eq@ instance.
instance Ord a => Ord (ModelInfo f a) where
  compare = compare `on` constValue

data SearchState f a model = SearchState {
    currentModel :: model,
    waitingDefs :: [(f a , a)]
  }

newtype SearchM f a model x = SearchM{ unSearchM :: StateT (SearchState f a model) [] x }
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)

runSearchM :: model -> SearchM f a model x -> [(x, model)]
runSearchM m0 mx = second currentModel <$> runStateT (unSearchM mx) (SearchState m0 [])

choose :: [a] -> SearchM f a model a
choose = SearchM . lift

maybeToSearch :: Maybe x -> SearchM f a model x
maybeToSearch = maybe mzero pure

enterDefsM :: Model f a model => [f a] -> a -> SearchM f a model ()
enterDefsM fas a = do
  m <- getsModel
  (m', newDefs) <- maybeToSearch $ enterDef fas a m
  putModel m'
  pushWaitingDefs newDefs

enterEqsM :: Model f a model => [f a] -> SearchM f a model ()
enterEqsM fas = do
  m <- getsModel
  (m', newDefs) <- maybeToSearch $ enterEqs fas m
  putModel m'
  pushWaitingDefs newDefs

getsModel :: SearchM f a model model
getsModel = SearchM $ State.gets currentModel

putModel :: model -> SearchM f a model ()
putModel m = SearchM $ State.modify $ \ss -> ss{ currentModel = m }

pushWaitingDefs :: [(f a, a)] -> SearchM f a model ()
pushWaitingDefs newDefs = SearchM $ State.modify $ \ss ->
  ss{ waitingDefs = newDefs ++ waitingDefs ss }

-- Gets all waitingDefs and remove them from the state
takeAllWaitingDefs :: SearchM f a model [(f a, a)]
takeAllWaitingDefs = SearchM $ State.state $ \ss ->
  (waitingDefs ss, ss{ waitingDefs = [] })

instance (Ord a, Ord (f a), Traversable f, Model f a model) => AnalysisM (SearchM f a model) (ModelInfo f a) (L f a) where
  makeA :: L f a (ModelInfo f a) -> SearchM f a model (ModelInfo f a)
  makeA (Con a) = pure $ ModelInfo (Just a) Set.empty
  makeA (Fun fm) = pure $ ModelInfo Nothing fnSet
    where
      fnSet = maybe Set.empty Set.singleton $ traverse constValue fm

  joinA :: ModelInfo f a -> ModelInfo f a -> SearchM f a model (ModelInfo f a)
  joinA d1 d2 = case (con1, con2) of
    (Nothing, Nothing) -> do
      let eqn = take 1 (Set.toList fun1) ++ take 1 (Set.toList fun2)
      enterEqsM eqn
      pure $ ModelInfo Nothing fun'
    (Nothing, Just a2) -> do
      enterDefsM (Set.toList fun1) a2
      pure $ ModelInfo (Just a2) fun'
    (Just a1, Nothing) -> do
      enterDefsM (Set.toList fun2) a1
      pure $ ModelInfo (Just a1) fun'
    (Just a1, Just a2) -> do
      guard (a1 == a2)
      pure $ ModelInfo (Just a1) fun'
    where
      ModelInfo con1 fun1 = d1
      ModelInfo con2 fun2 = d2
      fun' = Set.union fun1 fun2

  {-
  -- | We don't need custom modifyA because of the assumption
  -- 
  -- - equations contain every "constant function call"
  --
  -- and any node eventually became "constant function call" will be
  -- simultaneously merged with a class containing that
  -- constant function call.
  modifyA _ = pure
  -}

-- * Model search algorithm

solve :: (Ord a, Language f, Model f a model)
  => [a]
  -> [Property f]
  -> Map (f a) a
  -> model
  -> [model]
solve univ props = solveEqs eqs
  where
    eqs = props >>= runProperty univ

solveEqs :: (Ord a, Language f, Model f a model)
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> model
  -> [model]
solveEqs eqs knownDefs model0 = snd <$> runSearchM model0 (solveBody eqs knownDefs)

-- Shorthand
type EG f a = EGraph (ModelInfo f a) (L f a)

solveBody :: forall a f model. (Ord a, Language f, Model f a model)
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> SearchM f a model ()
solveBody eqs knownDefs = do
  eg1 <- initialize eqs knownDefs
  loop eg1
  where
    loop :: EG f a -> SearchM f a model ()
    loop eg = case whatToGuess eg of
      [] -> pure ()
      (fa : _) -> do
        m <- getsModel
        a <- choose $ guess fa m
        eg' <- syncLoop eg [defToEq (fa, a)] 
        loop eg'

initialize :: (Ord a, Language f, Model f a model)
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> SearchM f a model (EG f a)
initialize eqs knownDefs = do
  model0 <- getsModel
  (newDefs, model1) <- maybeToSearch $ updateModelDefs model0 knownEntries
  putModel model1
  let defs = Map.union newDefs knownDefs
  eg1 <- equateDefs (Map.toList defs) emptyEGraph
  syncLoop eg1 eqs
  where
    transposedDefs = transposeMap knownDefs
    knownEntries = (\(a, fas) -> (fas, Just a)) <$> Map.toList transposedDefs

updateModelDefs :: (Ord a, Language f, Model f a model)
  => model -> [(Set (f a), Maybe a)] -> Maybe (Map (f a) a, model)
updateModelDefs m0 entries = loopKnown m0 [] entries
  where
    alreadyKnownDefs = Set.unions
      [ fas | (fas, Just _) <- entries ]
    
    loopKnown m next [] = loop m [] (concat next)
    loopKnown m next ((fas, ma) : rest) = do
      (m', newDefs) <- case ma of
        Nothing -> enterEqs (Set.toList fas) m
        Just a  -> enterDef (Set.toList fas) a m
      loopKnown m' (newDefs : next) rest
    
    loop m acc [] = pure (Map.withoutKeys (Map.fromList acc) alreadyKnownDefs, m)
    loop m acc ((fa, a) : rest) = do
      (m', newDefs) <- enterDef [fa] a m
      loop m' ((fa, a) : acc) (newDefs ++ rest)

syncLoop :: (Ord a, Language f, Model f a model)
  => EG f a -> [(Term f a, Term f a)] -> SearchM f a model (EG f a)
syncLoop eg [] = pure eg
syncLoop eg eqs = do
  eg1 <- equateTerms eqs eg
  eg2 <- rebuildM eg1
  updates <- takeAllWaitingDefs
  updatesMap <- maybeToSearch $ mapFromListUnique updates
  let defs = map (\(a, fas) -> (fas, Just a)) $ Map.toList $ transposeMap updatesMap
  m <- getsModel
  (newDefs, m') <- maybeToSearch $ updateModelDefs m defs
  putModel m'
  syncLoop eg2 (defToEq <$> Map.toList newDefs)

whatToGuess :: (Ord a, Language f) => EG f a -> [f a]
whatToGuess = concatMap getConstFunList . sortOn (Down . getParentCount) . filter isUnknownValue . toListOf _classes
  where
    isUnknownValue cls = isNothing $ constValue (cls ^. _data)
    getParentCount cls = sizeSL (cls ^. _parents)
    getConstFunList = Set.toList . constFunctions . view _data

defToEq :: Functor f => (f a, a) -> (Term f a, Term f a)
defToEq = bimap liftFun con

equateDefs :: (Ord a, Language f, Model f a model)
  => [(f a, a)] -> EG f a -> SearchM f a model (EG f a)
equateDefs defs = equateTerms (defToEq <$> defs)

equateTerms :: (Ord a, Language f, Model f a model)
  => [(Term f a, Term f a)] -> EG f a -> SearchM f a model (EG f a)
equateTerms [] eg = pure eg
equateTerms ((lhs, rhs) : rest) eg = do
  (cLHS, eg1) <- representM lhs eg
  (cRHS, eg2) <- representM rhs eg1
  (_, eg3) <- mergeM cLHS cRHS eg2
  equateTerms rest eg3

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
toListOf trav = reify . foldMapOf trav (\a -> Endo (a:))
  where
    reify endo = appEndo endo []
