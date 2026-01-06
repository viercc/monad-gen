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

module ModelFinder.Dependent.Expr(
  -- * Expression type
  Expr(..),
  Requests(..),
  call,
  lift0, lift1, lift2, lift3,

  getDemands,  
  evaluate,
  evaluateReq,
  reduce,

  
  -- * Equational properties
  Property,
  equals, (===), evaluatesTo, satisfies,
  getDemandsProperty,
  reduceProperty, reducePropertyWith,
  evaluateProperty, evaluatePropertyWith,

  SimpleProp(..),
  reduceSimpleProp,
  reduceSimplePropWith,
  evaluateSimpleProp,
  evaluateSimplePropWith,

  -- * Aux types
  IsChanged(..)
) where

import Control.Monad ((>=>))
import Data.Bifunctor (Bifunctor (..))
import Control.Applicative (liftA3)
import Data.Constraint.Extras (Has (..))
import Data.Some (Some (..))

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

lift0 :: f x -> Expr f x
lift0 = Call

lift1 :: (x -> f y) -> Expr f x -> Expr f y
lift1 con ex = ex >>= \x -> Call (con x)

lift2 :: (x1 -> x2 -> f y) -> Expr f x1 -> Expr f x2 -> Expr f y
lift2 con ex1 ex2 = liftA2 (,) ex1 ex2 >>= \(x1,x2) -> Call (con x1 x2)

lift3 :: (x1 -> x2 -> x3 -> f y) -> Expr f x1 -> Expr f x2 -> Expr f x3 -> Expr f y
lift3 con ex1 ex2 ex3 = liftA3 (,,) ex1 ex2 ex3 >>= \(x1,x2,x3) -> Call (con x1 x2 x3)

-- | Get a list of unknonws required to progree evaluation
getDemands :: Expr f a -> [ Some f ]
getDemands e = case e of
  Pure _ -> []
  Call fx -> [ Some fx ]
  Demand fx _ -> reqToList fx

reqToList :: Requests f xs -> [ Some f ]
reqToList = ($ []) . go
  where
    go :: forall f r. Requests f r -> [ Some f ] -> [ Some f ]
    go (Request fx) = (Some fx :)
    go (RequestBoth r1 r2) = go r1 . go r2

-- | Evaluate an expression with monadic effect.
evaluate :: forall f m a. (Monad m) => (forall x. f x -> m x) -> Expr f a -> m a
evaluate ev = go
  where
    go (Pure a) = pure a
    go (Call fx) = evaluateReq ev (Request fx)
    go (Demand req cont) = evaluateReq ev req >>= \vs -> go (cont vs)

-- | Evaluate requests
evaluateReq :: forall f m a. (Monad m) => (forall x. f x -> m x) -> Requests f a -> m a
evaluateReq ev = go
  where
    go :: forall r. Requests f r -> m r
    go (Request fx) = ev fx
    go (RequestBoth r1 r2) = (,) <$> go r1 <*> go r2

-- | Reduce expression as much as you can.
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

-- * Equational properties

data SimpleProp f where
  -- | Constant failure or constant success
  PropBool :: !Bool -> SimpleProp f
  -- | Determines an unknown to a value
  PropDef :: !(f x) -> !x -> SimpleProp f
  -- | Two unknowns are equal
  PropSimpleEq :: !(f x) -> !(f x) -> SimpleProp f
  -- | Impose restriction on an unknown value
  PropSimplePred :: !(f x) -> (x -> Bool) -> SimpleProp f

type Property f = Expr f (SimpleProp f)

infix 1 `equals`
infix 1 ===

equals, (===) :: Eq x => Expr f x -> Expr f x -> Property f
equals (Pure x1) y = evaluatesTo y x1
equals x (Pure y1) = evaluatesTo x y1
equals (Call fx) (Call fy) = Pure $ PropSimpleEq fx fy
equals (Call fx) (Demand fy ky) =
  Demand (RequestBoth (Request fx) fy) $ \(x,ys) ->
    evaluatesTo (ky ys) x
equals (Demand fx kx) (Call fy) = Demand (RequestBoth fx (Request fy)) $ \(xs, y) ->
  evaluatesTo (kx xs) y
equals (Demand fx kx) (Demand fy ky) = Demand (RequestBoth fx fy) $ \(xs, ys) ->
  equals (kx xs) (ky ys)

(===) = equals

infix 1 `evaluatesTo`

evaluatesTo :: Eq x => Expr f x -> x -> Property f
evaluatesTo (Pure x) y = Pure $ PropBool (x == y)
evaluatesTo (Call fx) y = Pure $ PropDef fx y
evaluatesTo (Demand fx kx) y = Demand fx $ \xs -> evaluatesTo (kx xs) y

infix 1 `satisfies`

satisfies :: Expr f x -> (x -> Bool) -> Property f
satisfies (Pure x) p = Pure $ PropBool (p x)
satisfies (Call fx) p = Pure $ PropSimplePred fx p
satisfies (Demand fx kx) p = Demand fx $ \xs -> kx xs `satisfies` p

reducePropertyWith :: forall f. (forall x. f x -> x -> x -> Bool) -> (forall x. f x -> Maybe x) -> Property f -> (IsChanged, Property f)
reducePropertyWith getEq ev prop = case reduce ev prop of
  (changed, prop') -> case prop' of
    Pure simpleProp -> case reduceSimplePropWith getEq ev simpleProp of
      (changedSimpl, simpleProp') -> (changed <> changedSimpl, Pure simpleProp')
    _ -> (changed, prop')

reduceProperty :: forall f. (Has Eq f) => (forall x. f x -> Maybe x) -> Property f -> (IsChanged, Property f)
reduceProperty = reducePropertyWith hasEq

hasEq :: Has Eq f => f x -> x -> x -> Bool
hasEq fx = has @Eq fx (==)

reduceSimpleProp :: forall f. (Has Eq f) => (forall x. f x -> Maybe x) -> SimpleProp f -> (IsChanged, SimpleProp f)
reduceSimpleProp = reduceSimplePropWith hasEq

reduceSimplePropWith :: forall f. (forall x. f x -> x -> x -> Bool) -> (forall x. f x -> Maybe x) -> SimpleProp f -> (IsChanged, SimpleProp f)
reduceSimplePropWith getEq ev p = case p of
  PropBool _ -> (NoChange, p)
  PropDef fx y -> case ev fx of
    Nothing -> (NoChange, p)
    Just x -> (Changed, PropBool (getEq fx x y))
  PropSimpleEq fx fy -> case (ev fx, ev fy) of
    (Nothing, Nothing) -> (NoChange, p)
    (Just x,  Nothing) -> (Changed, PropDef fy x)
    (Nothing, Just y)  -> (Changed, PropDef fx y)
    (Just x, Just y) -> (Changed, PropBool (getEq fx x y))
  PropSimplePred fx cond -> case ev fx of
    Nothing -> (NoChange, p)
    Just x -> (Changed, PropBool (cond x))

evaluatePropertyWith :: forall f m. (Monad m)
  => (forall x. f x -> x -> x -> Bool)
  -> (forall x. f x -> m x) -> Property f -> m Bool
evaluatePropertyWith getEq ev p = evaluate ev p >>= evaluateSimplePropWith getEq ev

evaluateSimplePropWith :: forall f m. (Applicative m)
  => (forall x. f x -> x -> x -> Bool)
  -> (forall x. f x -> m x) -> SimpleProp f -> m Bool
evaluateSimplePropWith getEq ev p = case p of
  PropBool b -> pure b
  PropDef fx y -> getEq fx y <$> ev fx
  PropSimpleEq fx fy -> liftA2 (getEq fx) (ev fx) (ev fy)
  PropSimplePred fx cond -> cond <$> ev fx

evaluateProperty :: forall f m. (Has Eq f, Monad m) => (forall x. f x -> m x) -> Property f -> m Bool
evaluateProperty = evaluatePropertyWith hasEq

evaluateSimpleProp :: forall f m. (Has Eq f, Applicative m) => (forall x. f x -> m x) -> SimpleProp f -> m Bool
evaluateSimpleProp = evaluateSimplePropWith hasEq

getDemandsProperty :: forall f. Property f -> [ Some f ]
getDemandsProperty p = case p of
  Pure simp -> case simp of
    PropBool _ -> []
    PropDef fx _ -> [ Some fx ]
    PropSimpleEq fx fy -> [ Some fx, Some fy ]
    PropSimplePred fx _ -> [ Some fx ]
  _ -> getDemands p

-- | Common type to express "is it changed?" flag
data IsChanged = NoChange | Changed
  deriving stock (Show, Eq)

instance Semigroup IsChanged where
  NoChange <> y = y
  Changed <> _ = Changed
