{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.PTraversable
  ( PTraversable (..),
    fmapDefault,
    foldMapDefault,
    traverseDefault,
    cardinality1,
    enum1,
    coenum1,
    WrappedPTraversable (..),
    Generically1 (..),
  )
where

import Control.Applicative
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Coerce
import Data.Functor.Compose (Compose ())
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Identity
import Data.Functor.Product (Product)
import Data.Functor.Sum (Sum)
import Data.Profunctor
import Data.Profunctor.Cartesian
import Data.Profunctor.Counting
import Data.Profunctor.Extra
import Data.Profunctor.Unsafe ((#.), (.#))
import Data.Transparent
import GHC.Generics

class (Functor t) => PTraversable t where
  {-# MINIMAL ptraverseWith #-}
  ptraverseWith ::
    (Cartesian p, Cocartesian p) =>
    (as -> t a) ->
    (t b -> bs) ->
    p a b ->
    p as bs

ptraverse :: forall t p a b. (PTraversable t, Cartesian p, Cocartesian p) => p a b -> p (t a) (t b)
ptraverse = ptraverseWith id id
{-# INLINEABLE ptraverse #-}

fmapDefault :: (PTraversable t) => (a -> b) -> t a -> t b
fmapDefault = ptraverse
{-# INLINEABLE fmapDefault #-}

foldMapDefault :: (PTraversable t, Monoid m) => (a -> m) -> t a -> m
foldMapDefault = runForget . ptraverse . Forget
{-# INLINEABLE foldMapDefault #-}

traverseDefault :: (PTraversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
traverseDefault = lowerCoYoStar . ptraverse . liftCoYoStar
{-# INLINEABLE traverseDefault #-}

enum1 :: (PTraversable t, Alternative f) => f a -> f (t a)
enum1 = runJoker . ptraverse . Joker
{-# INLINEABLE enum1 #-}

coenum1 :: (PTraversable t, Divisible f, Decidable f) => f b -> f (t b)
coenum1 = runClown . ptraverse . Clown
{-# INLINEABLE coenum1 #-}

cardinality1 :: forall t proxy. (PTraversable t) => proxy t -> Int -> Int
cardinality1 _ = getCounting . ptraverse @t . Counting
{-# INLINEABLE cardinality1 #-}

unGenerically1 :: Generically1 f a -> f a
unGenerically1 = coerce

instance (Generic1 t, PTraversable (Rep1 t)) => PTraversable (Generically1 t) where
  ptraverseWith f g = ptraverseWith (from1 . unGenerically1 . f) (g . Generically1 . to1)
  {-# INLINEABLE ptraverseWith #-}

deriving via (Generically1 Identity) instance PTraversable Identity

deriving via (Generically1 Maybe) instance PTraversable Maybe

deriving via (Generically1 []) instance PTraversable []

deriving via
  (Generically1 ((,) a))
  instance
    (Transparent a) => PTraversable ((,) a)

deriving via
  (Generically1 (Either a))
  instance
    (Transparent a) => PTraversable (Either a)

deriving via
  (Generically1 (Sum t u))
  instance
    (PTraversable t, PTraversable u) => PTraversable (Sum t u)

deriving via
  (Generically1 (Product t u))
  instance
    (PTraversable t, PTraversable u) => PTraversable (Product t u)

deriving via
  (Generically1 (Compose t u))
  instance
    (PTraversable t, PTraversable u) => PTraversable (Compose t u)

newtype WrappedPTraversable t a = WrapPTraversable {unwrapPTraversable :: t a}

instance (Eq a, PTraversable t) => Eq (WrappedPTraversable t a) where
  (==) = coerce $ ptraverse @t (Clown eqv)
    where
      eqv = Equivalence ((==) @a)

instance (Ord a, PTraversable t) => Ord (WrappedPTraversable t a) where
  compare = coerce $ ptraverse @t (Clown cmp)
    where
      cmp = Comparison (compare @a)

instance
  (Transparent a, PTraversable t) =>
  Transparent (WrappedPTraversable t a)
  where
  describeOn f g =
    ptraverseWith (unwrapPTraversable . f) (g . WrapPTraversable) describe

instance (PTraversable t) => Functor (WrappedPTraversable t) where
  fmap f = coerce (fmapDefault @t f)

instance (PTraversable t) => Foldable (WrappedPTraversable t) where
  foldMap f = coerce (foldMapDefault @t f)

instance (PTraversable t) => Traversable (WrappedPTraversable t) where
  traverse f = fmap WrapPTraversable . traverseDefault @t f . coerce

---- Generics ----

instance PTraversable V1 where
  ptraverseWith f _ _ = lmap (absurdV1 . f) proEmpty
  {-# INLINEABLE ptraverseWith #-}

absurdV1 :: V1 a -> b
absurdV1 v = case v of {}

instance PTraversable U1 where
  ptraverseWith _ g _ = rmap (const (g U1)) proUnit
  {-# INLINEABLE ptraverseWith #-}

instance PTraversable Par1 where
  ptraverseWith :: forall p a b as bs. (Cartesian p, Cocartesian p) => (as -> Par1 a) -> (Par1 b -> bs) -> p a b -> p as bs
  ptraverseWith = coerce (dimap :: (as -> a) -> (b -> bs) -> p a b -> p as bs)
  {-# INLINEABLE ptraverseWith #-}

instance (Transparent c) => PTraversable (K1 i c) where
  ptraverseWith f g _ = describeOn (unK1 #. f) (g .# K1)

instance (PTraversable f) => PTraversable (M1 i c f) where
  ptraverseWith f g = ptraverseWith (unM1 . f) (g . M1)
  {-# INLINEABLE ptraverseWith #-}

instance (PTraversable f) => PTraversable (Rec1 f) where
  ptraverseWith f g = ptraverseWith (unRec1 . f) (g . Rec1)
  {-# INLINEABLE ptraverseWith #-}

instance (PTraversable t, PTraversable u) => PTraversable (t :+: u) where
  ptraverseWith f g p = dimap f' g' $ ptraverse p +++ ptraverse p
    where
      f' as = case f as of
        L1 ta -> Left ta
        R1 ua -> Right ua
      g' = either (g . L1) (g . R1)
  {-# INLINEABLE ptraverseWith #-}

instance (PTraversable f, PTraversable g) => PTraversable (f :*: g) where
  ptraverseWith f g p = dimap f' g' $ ptraverse p *** ptraverse p
    where
      f' as = case f as of
        ta :*: ua -> (ta, ua)
      g' (ta, ua) = g (ta :*: ua)
  {-# INLINEABLE ptraverseWith #-}

instance
  (PTraversable t, PTraversable u) =>
  PTraversable (t :.: u)
  where
  ptraverseWith f g = ptraverseWith (unComp1 . f) (g . Comp1) . ptraverse
  {-# INLINEABLE ptraverseWith #-}
