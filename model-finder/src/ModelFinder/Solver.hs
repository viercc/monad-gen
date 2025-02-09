{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module ModelFinder.Solver(
  -- * Model
  Model(..),
  lookupModel,
  
  -- * Solvers

  -- | "Default" solve
  solve,

  -- | Brute force
  bruteforceSolve,

  -- | Solve but doesn't refine constraints  during solve
  solveNoRefine,

  -- * Solutions

  Solution(..),
  Def(..),
  constraintToSolution,
) where

import Control.Monad (guard, ap)
import Data.Constraint.Extras
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity
import Data.GADT.Compare
import Data.List (maximumBy, sortOn)
import Data.Map qualified as Map
import Data.Ord (comparing)
import Data.Set qualified as Set
import Data.Some
import Data.Maybe (isJust)
import Data.GADT.Show (GShow (..))
import Data.Foldable (toList)

import ModelFinder.Expr
import Data.Functor (($>))

-- * Cached execution

type Cache f = DMap.DMap f Identity

emptyCache :: Cache f
emptyCache = DMap.empty

newtype Cached f m a = Cached { runCached :: Cache f -> m (Cache f, a) }
  deriving Functor

instance Monad m => Applicative (Cached f m) where
  pure a = Cached $ \cache -> pure (cache, a)
  (<*>) = ap

instance Monad m => Monad (Cached f m) where
  ma >>= k = Cached $ \cache -> do
    (cache', a) <- runCached ma cache
    runCached (k a) cache'

cached :: forall f m a. (GCompare f, Monad m) => (forall x. f x -> m x) -> f a -> Cached f m a
cached ev fa = Cached $ \cache ->
  case DMap.lookup fa cache of
    Nothing -> ev fa >>= \x -> pure (DMap.insert fa (Identity x) cache, x)
    Just (Identity x) -> pure (cache, x)

-- Types for model search

data Model f = Model (DMap.DMap f Set.Set)

deriving instance (GShow f, Has' Show f Set.Set) => Show (Model f)

lookupModel :: (GCompare f) => f x -> Model f -> Set.Set x
lookupModel fx (Model rel) = DMap.findWithDefault Set.empty fx rel

lookupKnown :: (GCompare f) => f x -> Model f -> Maybe x
lookupKnown fx model =
  case Set.toList (lookupModel fx model) of
    [x] -> Just x
    _ -> Nothing

guess :: (GCompare f) => Model f -> f x -> [x]
guess model fx = Set.toList $ lookupModel fx model

tighten :: forall f x. (GCompare f, Has Ord f) => f x -> Set.Set x -> Model f -> Maybe (IsChanged, Model f)
tighten fx xs (Model rel) = getCompose $ fmap Model $ DMap.alterF fx upd rel
  where
    upd Nothing = Compose Nothing
    upd (Just xs') =
      has @Ord fx $
        let xs'' = Set.intersection xs xs'
            changed = if xs' == xs'' then NoChange else Changed
         in Compose $ guard (not (Set.null xs'')) *> pure (changed, Just xs'')

-- Blocker

newtype Blocker f k = Blocker {getBlockerMap :: Map.Map (Some f) (Set.Set k)}

instance (GCompare f, Ord k) => Semigroup (Blocker f k) where
  Blocker bm <> Blocker bm' = Blocker $ Map.unionWith Set.union bm bm'

instance (GCompare f, Ord k) => Monoid (Blocker f k) where
  mempty = Blocker Map.empty

mostWanted :: Blocker f k -> Maybe (Some f)
mostWanted blocker
  | Map.null bm = Nothing
  | otherwise = Just $ fst $ maximumBy (comparing (Set.size . snd)) $ Map.toList bm
  where
    bm = getBlockerMap blocker

demandSet :: forall f. (GCompare f) => Property f -> Set.Set (Some f)
demandSet = Set.fromList . getDemandsProperty

singleBlocker :: (GCompare f, Ord k) => (k, Property f) -> Blocker f k
singleBlocker (k,expr) = Blocker $ Map.fromSet (const (Set.singleton k)) (demandSet expr)

updateBlocker :: (GCompare f, Ord k) => k -> Set.Set (Some f) -> Set.Set (Some f) -> Blocker f k -> Blocker f k
updateBlocker k old new (Blocker bm) = Blocker bm''
  where
    deletion = old Set.\\ new
    addition = new Set.\\ old
    bm' = foldl' (\m f -> Map.adjust (Set.delete k) f m) bm (Set.toList deletion)
    bm'' = foldl' (\m f -> Map.adjust (Set.insert k) f m) bm' (Set.toList addition)

-- Refining

refineComplex :: (GCompare f, Has Ord f) => Int -> Model f -> Requests f xs -> (xs -> Property f) -> Maybe [DSum f Set.Set]
refineComplex limit model req cont
  | candidates `longerThan` limit = Just [] -- Giving up == no new constraints
  | null admissibleCaches = Nothing
  | otherwise = Just newConstraints
  where
    candidates = runCached (evaluateReq (cached (guess model)) req) emptyCache
    succeeds (cache, xs) = anyWithLimit limit snd $ runCached (evaluatePropertyOrd (cached (guess model)) (cont xs)) cache
    admissibleCaches = DMap.map (Set.singleton . runIdentity) . fst <$> filter succeeds candidates
    newConstraints = DMap.toList $ DMap.unionsWithKey (\fx xs1 xs2 -> has @Ord fx (Set.union xs1 xs2)) admissibleCaches

refineSimple :: (GCompare f, Has Ord f) => Model f -> SimpleProp f -> Maybe (IsDeleted, [DSum f Set.Set])
refineSimple model prop = case prop of
  PropBool False -> Nothing
  PropBool True  -> Just (DeleteIt, [])
  PropDef fx x   -> has @Ord fx $
    guard (x `Set.member` lookupModel fx model) $> (DeleteIt, [fx :=> Set.singleton x])
  PropSimpleEq fx fy -> has @Ord fx $
    let xs = lookupModel fx model
        ys = lookupModel fy model
        xys = Set.intersection xs ys
        changes = [ fx :=> xys | xs /= xys ] ++ [ fy :=> xys | ys /= xys ]
    in guard (not (Set.null xys)) $> (KeepIt, changes)
  PropSimplePred fx cond -> has @Ord fx $
    let xs = lookupModel fx model
        xs' = Set.filter cond xs
    in guard (not (Set.null xs')) $> (DeleteIt, [ fx :=> xs' | xs == xs' ])

data IsDeleted = DeleteIt | KeepIt

evaluatePropertyOrd :: (Has Ord f, Monad m) => (forall x. f x -> m x) -> Property f -> m Bool
evaluatePropertyOrd = evaluatePropertyWith (\fx -> has @Ord fx (==))

reducePropertyOrd :: (Has Ord f) => (forall x. f x -> Maybe x) -> Property f -> (IsChanged, Property f)
reducePropertyOrd = reducePropertyWith (\fx -> has @Ord fx (==))

-- | @as `longerThan` n@ is properly lazy version of @length as > n@
-- (doesn't stuck on infinite list etc.)
--
-- >>> longerThan "abc" <$> [1,2,3,4]
-- [False,False,True,True]
-- >>> longerThan (repeat 'a') <$> [1,2,3,4]
-- [False,False,False,False]
longerThan :: [a] -> Int -> Bool
longerThan = foldr (\_ f n -> n <= 0 || f (n - 1)) (const False)

-- | @anyWithLimit n p as@ is @any pred as@ but "gives up" on list of length more than
--   @n@, by defaulting to @True@.
anyWithLimit :: Int -> (a -> Bool) -> [a] -> Bool
anyWithLimit limit p as = or ((p <$> take limit as) ++ [True])

bruteforceSolve :: forall f k. (GCompare f, Has Ord f, Ord k) => Model f -> Map.Map k (Property f) -> [Model f]
bruteforceSolve (Model model) exprs = solutionToModel <$> filter validSolution solutions
  where
    solutions = DMap.fromDistinctAscList <$> traverse dsumToList (DMap.toAscList model)
    dsumToList (fx :=> xs) = [ fx :=> Identity x | x <- Set.toList xs ]
    validSolution sol = all (\expr -> reduceBySol sol expr) exprs
    reduceBySol sol expr = case reducePropertyOrd (\fx -> runIdentity <$> DMap.lookup fx sol) expr of
      (_, Pure (PropBool b)) -> b
      _ -> False
    solutionToModel = Model . DMap.map (Set.singleton . runIdentity)

data SolverState f k = SolverState (Model f) (Blocker f k) (Map.Map k (Property f))

solve :: forall f k. (GCompare f, Has Ord f, Ord k) => Int -> Model f -> Map.Map k (Property f) -> [Model f]
solve limit initialModel exprs0 = toList (visitExprs initialState (Map.keys exprs0)) >>= solveLoop
  where
    initialBlockers = foldl' (<>) mempty (singleBlocker <$> Map.toList exprs0)
    initialState = SolverState initialModel initialBlockers exprs0

    solveLoop :: SolverState f k -> [Model f]
    solveLoop state@(SolverState model blocker _) = case mostWanted blocker of
      Nothing -> [model]
      Just (Some fx) -> do
        x <- guess model fx
        (ks, state') <- toList (enter state fx x)
        state'' <- toList $ visitExprs state' (toList ks)
        solveLoop state''
    
    visitExprs :: SolverState f k -> [k] -> Maybe (SolverState f k)
    visitExprs state [] = Just state
    visitExprs state (k : exprStack) =
      case reducePropertyAt state k of
        Nothing -> visitExprs state exprStack
        Just (state', expr) -> do
          (state'', defs) <- refineState state' k expr
          (notifiedExprs, state''') <- tightenState state'' (sortOn newSetSize defs)
          visitExprs state''' (Set.toList notifiedExprs ++ exprStack)

    refineState state@(SolverState model blocker exprs) k p =
      case p of
        Pure sprop -> case refineSimple model sprop of
          Nothing -> Nothing
          Just (DeleteIt, defs) ->
            let exprs' = Map.delete k exprs
                blocker' = updateBlocker k (demandSet p) (Set.empty) blocker
            in Just (SolverState model blocker' exprs', defs)
          Just (KeepIt, defs)  -> Just (state, defs)
        Call fx -> refineComplex limit model (Request fx) Pure >>= \defs -> Just (state, defs)
        Demand fx kx -> refineComplex limit model fx kx >>= \defs -> Just (state, defs)

    newSetSize (_ :=> xs) = Set.size xs

enter :: forall f k x. (GCompare f, Has Ord f, Ord k) => SolverState f k -> f x -> x -> Maybe (Set.Set k, SolverState f k)
enter (SolverState model blocker exprs) fx x = do
  (_, model') <- tighten fx (Set.singleton x) model
  let notifiedExprs = Map.findWithDefault Set.empty (Some fx) (getBlockerMap blocker)
      blocker' = Blocker $ Map.delete (Some fx) (getBlockerMap blocker)
  pure (notifiedExprs, SolverState model' blocker' exprs)

tightenState :: (GCompare f, Has Ord f, Ord k) => SolverState f k -> [DSum f Set.Set] -> Maybe (Set.Set k, SolverState f k)
tightenState = go Set.empty
  where
    go acc state [] = Just (acc, state)
    go acc state@(SolverState model blocker exprs) ((fx :=> xs) : defs) =
      case tighten fx xs model of
        Nothing -> Nothing
        Just (NoChange, _) | Set.size xs >= 2 -> go acc state defs
        Just (_, model') ->
          let notifiedExprs = Map.findWithDefault Set.empty (Some fx) (getBlockerMap blocker)
              blocker'
                | isJust (lookupKnown fx model') = Blocker $ Map.delete (Some fx) (getBlockerMap blocker)
                | otherwise = blocker
          in go (Set.union notifiedExprs acc) (SolverState model' blocker' exprs) defs

reducePropertyAt :: (GCompare f, Has Ord f, Ord k) => SolverState f k -> k -> Maybe (SolverState f k, Property f)
reducePropertyAt (SolverState model blocker exprs) k = do
  expr <- Map.lookup k exprs
  case reducePropertyOrd (`lookupKnown` model) expr of
    (NoChange, _) -> Nothing
    (Changed, expr') ->
      let exprs' = Map.insert k expr' exprs
          blocker' = updateBlocker k (demandSet expr) (demandSet expr') blocker
      in Just (SolverState model blocker' exprs', expr')

solveNoRefine :: forall f k. (GCompare f, Has Ord f, Ord k) => Model f -> Map.Map k (Property f) -> [Model f]
solveNoRefine initialModel exprs0 = toList (visitExprs initialState (Map.keys exprs0)) >>= go
  where
    initialBlockers = foldl' (<>) mempty (singleBlocker <$> Map.toList exprs0)
    initialState = SolverState initialModel initialBlockers exprs0

    go :: SolverState f k -> [Model f]
    go state@(SolverState model blocker _) = case mostWanted blocker of
      Nothing -> [model]
      Just (Some fx) -> do
        x <- guess model fx
        (ks, state') <- toList $ enter state fx x
        state'' <- toList $ visitExprs state' (Set.toList ks)
        go state''
    
    visitExprs :: SolverState f k -> [k] -> Maybe (SolverState f k)
    visitExprs state [] = Just state
    visitExprs state (k : exprStack) =
      case reducePropertyAt state k of
        Nothing -> visitExprs state exprStack
        Just (state', expr) -> do
          state'' <- refineState state' k expr
          visitExprs state'' exprStack

    refineState state@(SolverState model blocker exprs) k p =
      case p of
        Pure (PropBool False) -> Nothing
        Pure (PropBool True) -> Just (SolverState model blocker (Map.delete k exprs))
        _ -> Just state

data Def f = forall x. f x := x

instance (GShow f, Has Show f) => Show (Def f) where
  showsPrec p (fx := x) = showParen (p > 1) (gshowsPrec 1 fx . showString " := " . has @Show fx (showsPrec 1 x))

newtype Solution f = Solution [ Def f ]

deriving instance (GShow f, Has Show f) => Show (Solution f)

constraintToSolution :: Model f -> [Solution f]
constraintToSolution (Model m) = Solution <$> traverse (\(fx :=> xs) -> (fx :=) <$> Set.toList xs) (DMap.toList m)