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

module ModelFinder(
  Expr(..),
  Requests(..),
  call,

  Cache, lookupCache, emptyCache, addCache,

  evaluate, evaluateReq,
  reduce,

  IsChanged(..),
  
  ModelConstraint(..),
  lookupModel,
  lookupKnown,

  bruteforceSolve,
  solve,
  solveNoRefine,
  Def(..),
  Solution(..),
  constraintToSolution,

  guess, enter, tighten,

) where

import Control.Monad (guard, (>=>))
import Data.Bifunctor (Bifunctor (..))
import Data.Constraint.Extras
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity
import Data.GADT.Compare
import Data.List (maximumBy, sortBy)
import Data.Map qualified as Map
import Data.Ord (comparing)
import Data.Set qualified as Set
import Data.Some
import Data.Maybe (isJust)
import Data.GADT.Show (GShow (..))
import Data.Foldable (toList)

-- Expression with unknown functions

data Expr f a where
  Pure :: a -> Expr f a
  Call :: f v -> Expr f v
  Demand :: Requests f v -> (v -> Expr f a) -> Expr f a

data Expr' f a where
  Pure' :: a -> Expr' f a
  Demand' :: Requests f v -> (v -> Expr f a) -> Expr' f a

view :: Expr f a -> Expr' f a
view (Pure a) = Pure' a
view (Call fx) = Demand' (Request fx) Pure
view (Demand fx cont) = Demand' fx cont

data Requests f v where
  Request :: !(f v) -> Requests f v
  RequestBoth :: !(Requests f v1) -> !(Requests f v2) -> Requests f (v1, v2)

instance Functor (Expr f) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Call fv) = Demand (Request fv) (Pure . f)
  fmap f (Demand req cont) = Demand req (fmap f . cont)

instance Applicative (Expr f) where
  pure = Pure

  liftA2 f ex ey = case (view ex, view ey) of
    (Pure' x, Pure' y) -> Pure (x `f` y)
    (Pure' x, Demand' fy ky) -> Demand fy (fmap (x `f`) . ky)
    (Demand' fx kx, Pure' y) -> Demand fx (fmap (`f` y) . kx)
    (Demand' fx kx, Demand' fy ky) -> Demand (RequestBoth fx fy) (\(x, y) -> liftA2 f (kx x) (ky y))

instance Monad (Expr f) where
  Pure x >>= k = k x
  Call fx >>= k = Demand (Request fx) k
  Demand req cont >>= k = Demand req (cont >=> k)

call :: f x -> Expr f x
call = Call

-- Evaluate single expression

type Cache f = DMap.DMap f Identity

lookupCache :: (GCompare f) => f x -> Cache f -> Maybe x
lookupCache fx cache = runIdentity <$> DMap.lookup fx cache

emptyCache :: Cache f
emptyCache = DMap.empty

addCache :: (GCompare f) => f x -> x -> Cache f -> Cache f
addCache fx x cache = DMap.insert fx (Identity x) cache

evaluate :: forall f m a. (GCompare f, Monad m) => (forall x. f x -> m x) -> Cache f -> Expr f a -> m (Cache f, a)
evaluate ev = go
  where
    go :: forall r. Cache f -> Expr f r -> m (Cache f, r)
    go cache (Pure a) = pure (cache, a)
    go cache (Call fx) = evaluateReq ev cache (Request fx)
    go cache (Demand req cont) = evaluateReq ev cache req >>= \(cache', vs) -> go cache' (cont vs)

evaluateReq :: forall f m a. (GCompare f, Monad m) => (forall x. f x -> m x) -> Cache f -> Requests f a -> m (Cache f, a)
evaluateReq ev = handleReq
  where
    handleReq :: forall xs. Cache f -> Requests f xs -> m (Cache f, xs)
    handleReq cache (Request fx) =
      case DMap.lookup fx cache of
        Nothing ->
          ev fx >>= \x ->
            let cache' = DMap.insert fx (Identity x) cache
             in pure (cache', x)
        Just (Identity x) -> pure (cache, x)
    handleReq cache (RequestBoth r1 r2) =
      do
        (cache', x1) <- handleReq cache r1
        (cache'', x2) <- handleReq cache' r2
        pure (cache'', (x1, x2))

data IsChanged = NoChange | Changed
  deriving stock (Show, Eq)

instance Semigroup IsChanged where
  NoChange <> y = y
  Changed <> _ = Changed

reduce :: forall f a. (forall x. f x -> Maybe x) -> Expr f a -> (IsChanged, Expr f a)
reduce ev = go NoChange
  where
    go hasReducedOnce ma = case view ma of
      Pure' _ -> (hasReducedOnce, ma)
      Demand' req cont -> case reduceReq ev req of
        ReduceRemain NoChange _ _ -> (hasReducedOnce, ma)
        ReduceRemain Changed req' f -> (Changed, Demand req' (cont . f))
        ReduceComplete xs -> go Changed (cont xs)

data ReduceReq f xs where
  ReduceRemain :: IsChanged -> Requests f xs' -> (xs' -> xs) -> ReduceReq f xs
  ReduceComplete :: xs -> ReduceReq f xs

reduceReq :: forall f xs. (forall x. f x -> Maybe x) -> Requests f xs -> ReduceReq f xs
reduceReq ev req@(Request fx) = case ev fx of
  Nothing -> ReduceRemain NoChange req id
  Just x -> ReduceComplete x
reduceReq ev (RequestBoth req1 req2) = combineRed (reduceReq ev req1) (reduceReq ev req2)

combineRed :: ReduceReq f x -> ReduceReq f y -> ReduceReq f (x, y)
combineRed (ReduceRemain b1 r1 f) (ReduceRemain b2 r2 g) = ReduceRemain (b1 <> b2) (RequestBoth r1 r2) (bimap f g)
combineRed (ReduceRemain _ r1 f) (ReduceComplete y) = ReduceRemain Changed r1 (\x -> (f x, y))
combineRed (ReduceComplete x) (ReduceRemain _ r2 g) = ReduceRemain Changed r2 (\y -> (x, g y))
combineRed (ReduceComplete x) (ReduceComplete y) = ReduceComplete (x, y)

getBlockers :: forall f a. (GCompare f) => Expr f a -> Set.Set (Some f)
getBlockers (Pure _) = Set.empty
getBlockers (Call fx) = Set.singleton (Some fx)
getBlockers (Demand req _) = reqToSet req
  where
    reqToSet :: forall v. Requests f v -> Set.Set (Some f)
    reqToSet (Request fx) = Set.singleton (Some fx)
    reqToSet (RequestBoth r1 r2) = reqToSet r1 `Set.union` reqToSet r2

-- Types for model search

data ModelConstraint f = ModelConstraint (DMap.DMap f Set.Set)

deriving instance (GShow f, Has' Show f Set.Set) => Show (ModelConstraint f)

lookupModel :: (GCompare f) => f x -> ModelConstraint f -> Maybe (Set.Set x)
lookupModel fx (ModelConstraint rel) = DMap.lookup fx rel

lookupKnown :: (GCompare f) => f x -> ModelConstraint f -> Maybe x
lookupKnown fx model =
  lookupModel fx model >>= \xs ->
    case Set.toList xs of
      [x] -> Just x
      _ -> Nothing

guess :: (GCompare f) => ModelConstraint f -> f x -> [x]
guess model fx = case lookupModel fx model of
  Nothing -> []
  Just xs -> Set.toList xs

enter :: forall f x. (GCompare f, Has Ord f) => f x -> x -> ModelConstraint f -> Maybe (ModelConstraint f)
enter fx x (ModelConstraint rel) = ModelConstraint <$> DMap.alterF fx upd rel
  where
    upd Nothing = Nothing
    upd (Just xs) = has @Ord fx $ guard (x `Set.member` xs) *> pure (Just (Set.singleton x))

tighten :: forall f x. (GCompare f, Has Ord f) => f x -> Set.Set x -> ModelConstraint f -> Maybe (IsChanged, ModelConstraint f)
tighten fx xs (ModelConstraint rel) = getCompose $ fmap ModelConstraint $ DMap.alterF fx upd rel
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

singleBlocker :: (GCompare f, Ord k) => (k, Expr f a) -> Blocker f k
singleBlocker (k,expr) = Blocker $ Map.fromSet (const (Set.singleton k)) (getBlockers expr)

updateBlocker :: (GCompare f, Ord k) => k -> Set.Set (Some f) -> Set.Set (Some f) -> Blocker f k -> Blocker f k
updateBlocker k old new (Blocker bm) = Blocker bm''
  where
    deletion = old Set.\\ new
    addition = new Set.\\ old
    bm' = foldl' (\m f -> Map.adjust (Set.delete k) f m) bm (Set.toList deletion)
    bm'' = foldl' (\m f -> Map.adjust (Set.insert k) f m) bm' (Set.toList addition)

-- Refining

refine :: (GCompare f, Has Ord f) => Int -> ModelConstraint f -> Expr f Bool -> Maybe [DSum f Set.Set]
refine _ _ (Pure p) = if p then Just [] else Nothing
refine limit model (Call fx) = refine limit model (Demand (Request fx) Pure)
refine limit model (Demand req cont)
  | candidates `longerThan` limit = Just [] -- Giving up == no new constraints
  | null admissibleCaches = Nothing
  | otherwise = Just newConstraints
  where
    candidates = evaluateReq (guess model) emptyCache req
    succeeds (cache, xs) = anyWithLimit limit snd $ evaluate (guess model) cache (cont xs)
    admissibleCaches = DMap.map (Set.singleton . runIdentity) . fst <$> filter succeeds candidates
    newConstraints = DMap.toList $ DMap.unionsWithKey (\fx xs1 xs2 -> has @Ord fx (Set.union xs1 xs2)) admissibleCaches

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

bruteforceSolve :: forall f k. (GCompare f, Has Ord f, Ord k) => ModelConstraint f -> Map.Map k (Expr f Bool) -> [ModelConstraint f]
bruteforceSolve (ModelConstraint model) exprs = solutionToModel <$> filter validSolution solutions
  where
    solutions = DMap.fromDistinctAscList <$> traverse dsumToList (DMap.toAscList model)
    dsumToList (fx :=> xs) = [ fx :=> Identity x | x <- Set.toList xs ]
    validSolution sol = all (\expr -> reduceBySol sol expr) exprs
    reduceBySol sol expr = case reduce (\fx -> runIdentity <$> DMap.lookup fx sol) expr of
      (_, Pure b) -> b
      _ -> False
    solutionToModel = ModelConstraint . DMap.map (Set.singleton . runIdentity)

data SolverState f k = SolverState (ModelConstraint f) (Blocker f k) (Map.Map k (Expr f Bool))

solve :: forall f k. (GCompare f, Has Ord f, Ord k) => Int -> ModelConstraint f -> Map.Map k (Expr f Bool) -> [ModelConstraint f]
solve limit initialModel exprs0 = toList (propagate initialState (Map.keys exprs0) []) >>= go
  where
    initialBlockers = foldl' (<>) mempty (singleBlocker <$> Map.toList exprs0)
    initialState = SolverState initialModel initialBlockers exprs0

    go :: SolverState f k -> [ModelConstraint f]
    go state@(SolverState model blocker _) = case mostWanted blocker of
      Nothing -> [model]
      Just (Some fx) -> do
        x <- guess model fx
        case propagate state [] [fx :=> Set.singleton x] of
          Nothing -> []
          Just state' -> go state'
    
    propagate :: SolverState f k -> [k] -> [DSum f Set.Set] -> Maybe (SolverState f k)
    propagate state [] [] = Just state
    propagate state@(SolverState model blocker exprs) (k : exprStack) [] =
      case Map.lookup k exprs of
        Nothing -> propagate state exprStack []
        Just expr -> do
          (exprs', blocker', expr') <- reduceEquation model blocker exprs k expr
          defs <- refine limit model expr'
          propagate (SolverState model blocker' exprs') exprStack (sortBy (comparing newSetSize) defs)
    propagate state@(SolverState model blocker exprs) exprStack ((fx :=> xs) : defs) =
      case tighten fx xs model of
        Nothing -> Nothing
        Just (NoChange, _) | Set.size xs >= 2 -> propagate state exprStack defs
        Just (_, model') ->
          let notifiedExprs = Map.findWithDefault Set.empty (Some fx) (getBlockerMap blocker)
              blocker'
                | isJust (lookupKnown fx model') = Blocker $ Map.delete (Some fx) (getBlockerMap blocker)
                | otherwise = blocker
          in propagate (SolverState model' blocker' exprs) (Set.toList notifiedExprs ++ exprStack) defs

    reduceEquation :: ModelConstraint f -> Blocker f k -> Map.Map k (Expr f Bool) -> k -> Expr f Bool -> Maybe (Map.Map k (Expr f Bool),Blocker f k,Expr f Bool)
    reduceEquation model blocker exprs k expr = case reduce (`lookupKnown` model) expr of
        (_, expr'@(Pure True)) -> Just (Map.delete k exprs, blocker, expr')
        (_, Pure False) -> Nothing
        (NoChange, _) -> Just (exprs, blocker, expr)
        (Changed, expr') ->
          let exprs' = Map.insert k expr' exprs
              blocker' = updateBlocker k (getBlockers expr) (getBlockers expr') blocker
          in Just (exprs', blocker', expr')
    
    newSetSize (_ :=> xs) = Set.size xs

solveNoRefine :: forall f k. (GCompare f, Has Ord f, Ord k) => ModelConstraint f -> Map.Map k (Expr f Bool) -> [ModelConstraint f]
solveNoRefine initialModel exprs0 = toList (propagate initialState (Map.keys exprs0) []) >>= go
  where
    initialBlockers = foldl' (<>) mempty (singleBlocker <$> Map.toList exprs0)
    initialState = SolverState initialModel initialBlockers exprs0

    go :: SolverState f k -> [ModelConstraint f]
    go state@(SolverState model blocker _) = case mostWanted blocker of
      Nothing -> [model]
      Just (Some fx) -> do
        x <- guess model fx
        case propagate state [] [fx :=> Set.singleton x] of
          Nothing -> []
          Just state' -> go state'
    
    propagate :: SolverState f k -> [k] -> [DSum f Set.Set] -> Maybe (SolverState f k)
    propagate state [] [] = Just state
    propagate state@(SolverState model blocker exprs) (k : exprStack) [] =
      case Map.lookup k exprs of
        Nothing -> propagate state exprStack []
        Just expr -> do
          (exprs', blocker', _) <- reduceEquation model blocker exprs k expr
          propagate (SolverState model blocker' exprs') exprStack []
    propagate state@(SolverState model blocker exprs) exprStack ((fx :=> xs) : defs) =
      case tighten fx xs model of
        Nothing -> Nothing
        Just (NoChange, _) | Set.size xs >= 2 -> propagate state exprStack defs
        Just (_, model') ->
          let notifiedExprs = Map.findWithDefault Set.empty (Some fx) (getBlockerMap blocker)
              blocker'
                | isJust (lookupKnown fx model') = Blocker $ Map.delete (Some fx) (getBlockerMap blocker)
                | otherwise = blocker
          in propagate (SolverState model' blocker' exprs) (Set.toList notifiedExprs ++ exprStack) defs

    reduceEquation :: ModelConstraint f -> Blocker f k -> Map.Map k (Expr f Bool) -> k -> Expr f Bool -> Maybe (Map.Map k (Expr f Bool),Blocker f k,Expr f Bool)
    reduceEquation model blocker exprs k expr = case reduce (`lookupKnown` model) expr of
        (_, expr'@(Pure True)) -> Just (Map.delete k exprs, blocker, expr')
        (_, Pure False) -> Nothing
        (NoChange, _) -> Just (exprs, blocker, expr)
        (Changed, expr') ->
          let exprs' = Map.insert k expr' exprs
              blocker' = updateBlocker k (getBlockers expr) (getBlockers expr') blocker
          in Just (exprs', blocker', expr')

data Def f = forall x. f x := x

instance (GShow f, Has Show f) => Show (Def f) where
  showsPrec p (fx := x) = showParen (p > 1) (gshowsPrec 1 fx . showString " := " . has @Show fx (showsPrec 1 x))

newtype Solution f = Solution [ Def f ]

deriving instance (GShow f, Has Show f) => Show (Solution f)

constraintToSolution :: ModelConstraint f -> [Solution f]
constraintToSolution (ModelConstraint m) = Solution <$> traverse (\(fx :=> xs) -> (fx :=) <$> Set.toList xs) (DMap.toList m)