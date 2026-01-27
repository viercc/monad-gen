{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module ModelFinder.Dependent.Solver(
  -- * Model
  Model(..),
  lookupModel,
  
  -- * Solvers

  -- | "Default" solve
  solve,

  -- * Solutions

  Solution(..),
  Def(..),
  constraintToSolution,
) where

import Control.Monad (guard)
import Data.Constraint.Extras
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Functor.Compose (Compose (..))
import Data.GADT.Compare
import Data.List (maximumBy)

import Data.IntMap.Strict qualified as IntMap

import Data.Map qualified as Map
import Data.Ord (comparing)
import Data.Set qualified as Set
import Data.Some
import Data.Maybe (isJust)
import Data.GADT.Show (GShow (..))
import Data.Foldable (toList)

import ModelFinder.Dependent.Expr
import Data.Functor (($>))

-- Types for model search

newtype Model f = Model (DMap.DMap f Set.Set)

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

type PropertyId = Int
newtype Blocker f = Blocker { getBlockerMap :: Map.Map (Some f) (Set.Set Int) }

instance (GCompare f) => Semigroup (Blocker f) where
  Blocker bm <> Blocker bm' = Blocker $ Map.unionWith Set.union bm bm'

instance (GCompare f) => Monoid (Blocker f) where
  mempty = Blocker Map.empty

mostWanted :: Blocker f -> Maybe (Some f)
mostWanted blocker
  | Map.null bm = Nothing
  | otherwise = Just $ fst $ maximumBy (comparing (Set.size . snd)) $ Map.toList bm
  where
    bm = getBlockerMap blocker

demandSet :: forall f. (GCompare f) => Property f -> Set.Set (Some f)
demandSet = Set.fromList . getDemandsProperty

updateBlocker :: (GCompare f) => PropertyId -> Set.Set (Some f) -> Set.Set (Some f) -> Blocker f -> Blocker f
updateBlocker k old new (Blocker bm) = Blocker bm''
  where
    deletion = old Set.\\ new
    addition = new Set.\\ old
    deleteFromSet xs x = case Set.delete x xs of
      xs' | Set.null xs' -> Nothing
          | otherwise    -> Just xs'
    bm' = Map.differenceWith deleteFromSet bm (Map.fromSet (const k) deletion)
    bm'' = Map.unionWith Set.union bm' (Map.fromSet (const (Set.singleton k)) addition)

-- Refining

refineSimple :: (GCompare f, Has Ord f) => Model f -> SimpleProp f -> Maybe (IsDeleted, [DSum f Set.Set])
refineSimple model prop = case prop of
  PropFail -> Nothing
  PropSuccess -> Just (DeleteIt, [])
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
  deriving (Show)

reducePropertyOrd :: (Has Ord f) => (forall x. f x -> Maybe x) -> Property f -> (IsChanged, Property f)
reducePropertyOrd = reducePropertyWith (\fx -> has @Ord fx (==))

type PropertyMap f = IntMap.IntMap (Property f)

data SolverState f = SolverState {
    _currentModel :: !(Model f),
    _blockers :: !(Blocker f),
    _allProps :: !(PropertyMap f)
  }

solve :: forall f. (GCompare f, Has Ord f) => Model f -> [Property f] -> [Model f]
solve initialModel exprsList = initialize >>= solveLoop
  where
    exprs = IntMap.fromList (zip [0..] exprsList)
    initialState = SolverState initialModel mempty exprs

    initialize :: [SolverState f]
    initialize = toList $ do
      (state', defs) <- visitExprsFirstTime initialState (IntMap.keys exprs)
      tightenState state' defs

    solveLoop :: SolverState f -> [Model f]
    solveLoop state@(SolverState model blocker _) = case mostWanted blocker of
      Nothing -> [model]
      Just (Some fx) -> do
        x <- guess model fx
        state' <- toList (enter state fx x)
        solveLoop state'

enter :: forall f x. (GCompare f, Has Ord f) => SolverState f -> f x -> x -> Maybe (SolverState f)
enter state fx x = tightenState state [fx :=> Set.singleton x]

visitExprsFirstTime :: (GCompare f, Has Ord f) => SolverState f -> [PropertyId] -> Maybe (SolverState f, [DSum f Set.Set])
visitExprsFirstTime = loop []
  where
    loop acc state [] = Just (state, concat acc)
    loop acc state (k : ks) = do
      (state', defs) <- visitExprFirstTime state k
      loop (defs : acc) state' ks

visitExprFirstTime :: (GCompare f, Has Ord f) => SolverState f -> PropertyId -> Maybe (SolverState f, [DSum f Set.Set])
visitExprFirstTime (SolverState model blocker exprs) k = do
  expr <- IntMap.lookup k exprs
  -- Reduce the expr, and regardless of if it was changed or not,
  -- update blocker map.
  (expr', keeps, defs) <- case snd (reducePropertyOrd (`lookupKnown` model) expr) of
    Pure sprop -> do
      (keeps, defs) <- refineSimple model sprop
      pure (Pure sprop, keeps, defs)
    expr' -> pure (expr', KeepIt, [])
  case keeps of
    KeepIt -> do
      let exprs' = IntMap.insert k expr' exprs
          blocker' = updateBlocker k Set.empty (demandSet expr') blocker
      pure (SolverState model blocker' exprs', defs)
    DeleteIt -> do
      let exprs' = IntMap.delete k exprs
      pure (SolverState model blocker exprs', defs)

visitExpr :: (GCompare f, Has Ord f) => SolverState f -> PropertyId -> Maybe (SolverState f, [DSum f Set.Set])
visitExpr state@(SolverState model blocker exprs) k = do
  expr <- IntMap.lookup k exprs
  case reducePropertyOrd (`lookupKnown` model) expr of
    (NoChange, _) -> pure (state, [])
    (Changed, expr') -> do
      (keeps, defs) <- case expr' of
        Pure sprop -> refineSimple model sprop
        _ -> pure (KeepIt, [])
      case keeps of
        KeepIt -> do
          let exprs' = IntMap.insert k expr' exprs
              blocker' = updateBlocker k (demandSet expr) (demandSet expr') blocker
          pure (SolverState model blocker' exprs', defs)
        DeleteIt -> do
          let exprs' = IntMap.delete k exprs
              blocker' = updateBlocker k (demandSet expr) Set.empty blocker
          pure (SolverState model blocker' exprs', defs)

visitExprs :: (GCompare f, Has Ord f) => SolverState f -> [PropertyId] -> Maybe (SolverState f, [DSum f Set.Set])
visitExprs = loop []
  where
    loop acc state [] = Just (state, concat acc)
    loop acc state (k : ks) = do
      (state', defs) <- visitExpr state k
      loop (defs : acc) state' ks

tightenState :: (GCompare f, Has Ord f) => SolverState f -> [DSum f Set.Set] -> Maybe (SolverState f)
tightenState state [] = Just state
tightenState state@(SolverState model blocker exprs) ((fx :=> xs) : rest) = do
  (changes, model') <- tighten fx xs model
  case changes of
    NoChange -> tightenState state rest
    Changed  -> do
      let notifiedExprs = Map.findWithDefault Set.empty (Some fx) (getBlockerMap blocker)
          blocker'
            | isJust (lookupKnown fx model') = Blocker $ Map.delete (Some fx) (getBlockerMap blocker)
            | otherwise = blocker
          state' = SolverState model' blocker' exprs
      (state'', defs) <- visitExprs state' (Set.toList notifiedExprs)
      tightenState state'' (defs ++ rest)

data Def f = forall x. f x := x

instance (GShow f, Has Show f) => Show (Def f) where
  showsPrec p (fx := x) = showParen (p > 1) (gshowsPrec 1 fx . showString " := " . has @Show fx (showsPrec 1 x))

newtype Solution f = Solution [ Def f ]

deriving instance (GShow f, Has Show f) => Show (Solution f)

constraintToSolution :: Model f -> [Solution f]
constraintToSolution (Model m) = Solution <$> traverse (\(fx :=> xs) -> (fx :=) <$> Set.toList xs) (DMap.toList m)