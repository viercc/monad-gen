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

module ModelFinder.Expr(
  Expr(..),
  Requests(..),
  call,
  
  evaluate, evaluateReq,
  reduce,
  
  IsChanged(..)
) where

import Control.Monad ((>=>))
import Data.Bifunctor (Bifunctor (..))

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

evaluate :: forall f m a. (Monad m) => (forall x. f x -> m x) -> Expr f a -> m a
evaluate ev = go
  where
    go (Pure a) = pure a
    go (Call fx) = evaluateReq ev (Request fx)
    go (Demand req cont) = evaluateReq ev req >>= \vs -> go (cont vs)

evaluateReq :: forall f m a. (Monad m) => (forall x. f x -> m x) -> Requests f a -> m a
evaluateReq ev = go
  where
    go :: forall r. Requests f r -> m r
    go (Request fx) = ev fx
    go (RequestBoth r1 r2) = (,) <$> go r1 <*> go r2

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
