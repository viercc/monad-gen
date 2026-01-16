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
import Control.Applicative (Alternative((<|>)))
import Control.Monad ( guard, MonadPlus (..) )

import Data.Maybe (isNothing)
import Data.List (sortOn)
import Data.Ord (Down(..))
import Data.Functor.Const (Const(..))
import Data.Monoid (Endo(..))

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.State.Strict (StateT, MonadTrans (..), evalStateT)
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
    constFunctions :: !(Set (f a)),
    -- ^ The class contains (Fun fx) where each children
    --   classes of fx contain constant value a
    lastUpdated :: !Int
    -- ^ When the analysis data have changed
  }
  deriving (Show)

-- | This is a BAD hack! Changes of @constFunctions@
--   do not need to trigger repair of parents.
instance Eq a => Eq (ModelInfo f a) where
  (==) = (==) `on` constValue

-- | This is a BAD hack! See @Eq@ instance.
instance Ord a => Ord (ModelInfo f a) where
  compare = compare `on` constValue

newtype SearchM x = SearchM { unSearchM :: StateT Int [] x }
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)

runSearchM :: SearchM x -> [x]
runSearchM mx = evalStateT (unSearchM mx) 0

now :: SearchM Int
now = SearchM State.get

tick :: SearchM ()
tick = SearchM $ State.modify' (1 +)

choose :: [a] -> SearchM a
choose = SearchM . lift

maybeToSearch :: Maybe x -> SearchM x
maybeToSearch = maybe mzero pure

instance (Ord a, Ord (f a), Traversable f) => AnalysisM SearchM (ModelInfo f a) (L f a) where
  makeA :: L f a (ModelInfo f a) -> SearchM (ModelInfo f a)
  makeA (Con a) = ModelInfo (Just a) Set.empty <$> now
  makeA (Fun fm) = ModelInfo Nothing fnSet <$> now
    where
      fnSet = maybe Set.empty Set.singleton $ traverse constValue fm

  joinA :: ModelInfo f a -> ModelInfo f a -> SearchM (ModelInfo f a)
  joinA d1 d2 = do
    guard consistent
    t <- if hadNoChange then pure (lastUpdated d1) else now
    pure ModelInfo { constValue = con', constFunctions = fun', lastUpdated = t }
    where
      con1 = constValue d1
      con2 = constValue d2
      fun1 = constFunctions d1
      fun2 = constFunctions d2
      con' = con1 <|> con2
      fun' = Set.union fun1 fun2
      consistent = case (con1, con2) of
        (Just a1, Just a2) -> a1 == a2
        _ -> True
      hadNoChange = con1 == con2 && fun1 == fun2

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
solve univ props knownDefs model0 = runSearchM (solveBody eqs knownDefs model0)
  where
    eqs = props >>= runProperty univ

solveEqs :: (Ord a, Language f, Model f a model)
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> model
  -> [model]
solveEqs eqs knownDefs model0 = runSearchM (solveBody eqs knownDefs model0)

-- Shorthand
type EG f a = EGraph (ModelInfo f a) (L f a)

solveBody :: forall a f model. (Ord a, Language f, Model f a model)
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> model
  -> SearchM model
solveBody eqs knownDefs model0 = do
  (eg1, model1) <- initialize eqs knownDefs model0
  loop eg1 model1
  where
    loop :: EG f a -> model -> SearchM model
    loop eg m = case whatToGuess eg of
      [] -> pure m
      (fa : _) -> do
        a <- choose $ guess fa m
        (eg', m') <- syncLoop eg m [defToEq (fa, a)] 
        loop eg' m'

initialize :: (Ord a, Language f, Model f a model)
  => [(Term f a, Term f a)]
  -> Map (f a) a
  -> model
  -> SearchM (EG f a, model)
initialize eqs knownDefs model0 = do
  (newDefs, model1) <- maybeToSearch $ updateModelDefs model0 knownEntries
  let defs = Map.union newDefs knownDefs
  eg1 <- equateDefs (Map.toList defs) emptyEGraph
  syncLoop eg1 model1 eqs
  where
    transposedDefs = Map.fromListWith Set.union
      [ (a, Set.singleton fa) | (fa, a) <- Map.toList knownDefs ]
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
  => EG f a -> model -> [(Term f a, Term f a)] -> SearchM (EG f a, model)
syncLoop eg m [] = pure (eg, m)
syncLoop eg m eqs = do
  tick
  eg1 <- equateTerms eqs eg
  eg2 <- rebuildM eg1
  updates <- getLatestUpdates eg2
  (defs, m') <- maybeToSearch $ updateModelDefs m updates
  syncLoop eg2 m' (defToEq <$> Map.toList defs)

getLatestUpdates :: (Ord a, Language f)
  => EG f a -> SearchM [(Set (f a), Maybe a)]
getLatestUpdates eg = filteredUpdates <$> now
  where
    allClasses = toListOf (_classes . _data) eg
    getDefPart d = (constFunctions d, constValue d)
    filteredUpdates t = map getDefPart $ filter (\d -> lastUpdated d == t) allClasses

whatToGuess :: (Ord a, Language f) => EG f a -> [f a]
whatToGuess = concatMap getConstFunList . sortOn (Down . getParentCount) . filter isUnknownValue . toListOf _classes
  where
    isUnknownValue cls = isNothing $ constValue (cls ^. _data)
    getParentCount cls = sizeSL (cls ^. _parents)
    getConstFunList = Set.toList . constFunctions . view _data

defToEq :: Functor f => (f a, a) -> (Term f a, Term f a)
defToEq = bimap liftFun con

equateDefs :: (Ord a, Language f)
  => [(f a, a)] -> EG f a -> SearchM (EG f a)
equateDefs defs = equateTerms (defToEq <$> defs)

equateTerms :: (Ord a, Language f)
  => [(Term f a, Term f a)] -> EG f a -> SearchM (EG f a)
equateTerms [] eg = pure eg
equateTerms ((lhs, rhs) : rest) eg = do
  (cLHS, eg1) <- representM lhs eg
  (cRHS, eg2) <- representM rhs eg1
  (_, eg3) <- mergeM cLHS cRHS eg2
  equateTerms rest eg3

----

type LensLike f s t a b = (a -> f b) -> s -> f t

foldMapOf :: LensLike (Const m) s t a b -> (a -> m) -> s -> m
foldMapOf trav f = getConst . trav (Const . f)

toListOf :: LensLike (Const (Endo [a])) s t a b -> s -> [a]
toListOf trav = reify . foldMapOf trav (\a -> Endo (a:))
  where
    reify endo = appEndo endo []
