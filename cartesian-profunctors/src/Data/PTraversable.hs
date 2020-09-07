{-# LANGUAGE
  ScopedTypeVariables,
  TypeApplications,
  RankNTypes,
  
  EmptyCase,
  TypeOperators,
  TupleSections,
  
  DerivingVia,
  DeriveTraversable,
  StandaloneDeriving,
  UndecidableInstances,
  QuantifiedConstraints
#-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Data.PTraversable(
  PTraversable(..),
  fmapDefault,
  foldMapDefault,
  traverseDefault,
  size1,
  enum1,
  coenum1,
  
  ptraverseSlow,
  enum1Slow,
  coenum1Slow,
  WrappedPTraversable(..),
  
  Generically1(..),
  GPTraversable'(),

  -- * Utility
  Representational1,
  Representational2
) where

import GHC.Generics
import Generic.Data(Generically1(..), GFoldable, GTraversable)
import Data.Coerce

import Control.Applicative
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Identity
import Data.Bifunctor.Joker
import Data.Bifunctor.Clown

import Data.Profunctor
import Data.Profunctor.Yoneda (Yoneda(..), extractYoneda)
import Data.Profunctor.Monad (proreturn)
import Data.Profunctor.Cartesian
import Data.Profunctor.Extra
import Data.Profunctor.Counting

import Data.Transparent

import Data.Coerce.Extra

class (Traversable t) => PTraversable t where
  ptraverse :: (Representational2 p, Cartesian p, Cocartesian p)
                => p a b -> p (t a) (t b)

instance (Traversable t, Generic1 t, GPTraversable' (Rep1 t))
         => PTraversable (Generically1 t) where
  ptraverse = dimap (from1 . unGenerically1) (Generically1 . to1) . ptraverse'
  {-# INLINEABLE ptraverse #-}

deriving via (Generically1 Identity) instance PTraversable Identity
deriving via (Generically1 Maybe) instance PTraversable Maybe
deriving via (Generically1 []) instance PTraversable []
deriving via (Generically1 ((,) a))
  instance Transparent a => PTraversable ((,) a)
deriving via (Generically1 (Either a))
  instance Transparent a => PTraversable (Either a)

instance (PTraversable f, PTraversable g) => PTraversable (f :.: g) where
  ptraverse = coerceDimap unComp1 Comp1 . ptraverse . ptraverse
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

newtype WrappedPTraversable t a = WrapPTraversable { unwrapPTraversable :: t a }

instance (Eq a, PTraversable t) => Eq (WrappedPTraversable t a) where
  (==) = coerce $ ptraverse @t (Clown eqv)
    where eqv = Equivalence ((==) @a)

instance (Ord a, PTraversable t) => Ord (WrappedPTraversable t a) where
  compare = coerce $ ptraverse @t (Clown cmp)
    where cmp = Comparison (compare @a)

instance (Transparent a, PTraversable t)
         => Transparent (WrappedPTraversable t a) where
  describe = coerceDimap unwrapPTraversable WrapPTraversable $
    ptraverse @t (describe @a)

instance (PTraversable t) => Functor (WrappedPTraversable t) where
  fmap f = coerce (fmapDefault @t f)

instance (PTraversable t) => Foldable (WrappedPTraversable t) where
  foldMap f = coerce (foldMapDefault @t f)

instance (PTraversable t) => Traversable (WrappedPTraversable t) where
  traverse f = fmap WrapPTraversable . traverseDefault @t f . coerce

size1 :: forall t proxy. (PTraversable t) => proxy t -> Int -> Int
size1 _ = getCounting . ptraverse @t . Counting
{-# INLINEABLE size1 #-}

enum1 :: (PTraversable t, Alternative f, Representational1 f)
      => f a -> f (t a)
enum1 = runJoker . ptraverse . Joker
{-# INLINEABLE enum1 #-}

coenum1 :: (PTraversable t, Decidable f, Representational1 f)
        => f a -> f (t a)
coenum1 = runClown . ptraverse . Clown
{-# INLINEABLE coenum1 #-}

-- | 'ptraverse', but doesn't require 'Representational2' at expence of
--   some cost incurred.
ptraverseSlow :: forall t p a b. (PTraversable t, Cartesian p, Cocartesian p)
          => p a b -> p (t a) (t b)
ptraverseSlow = extractYoneda . ptraverse @t @(Yoneda p) . proreturn
{-# INLINEABLE ptraverseSlow #-}

-- | 'enum1', but doesn't require 'Representational1' at expence of
--   some cost incurred.
enum1Slow :: (PTraversable t, Alternative f) => f a -> f (t a)
enum1Slow = lowerCoYoJoker . ptraverse . liftCoYoJoker
{-# INLINEABLE enum1Slow #-}

-- | 'coenum1', but doesn't require 'Representational1' at expence of
--   some cost incurred.
coenum1Slow :: (PTraversable t, Decidable f) => f a -> f (t a)
coenum1Slow = lowerCoYoClown . ptraverse . liftCoYoClown
{-# INLINEABLE coenum1Slow #-}

-------------------------------------
-- Generics

class (Functor t, GFoldable t, GTraversable t) => GPTraversable' t where
  ptraverse' :: (Representational2 p, Cartesian p, Cocartesian p)
             => p a b -> p (t a) (t b)

instance GPTraversable' V1 where
  ptraverse' _ = lmap absurdV1 proEmpty
  {-# INLINEABLE ptraverse' #-}

absurdV1 :: V1 a -> b
absurdV1 v = case v of { }

instance GPTraversable' U1 where
  ptraverse' _ = rmap (const U1) proUnit
  {-# INLINEABLE ptraverse' #-}

instance GPTraversable' Par1 where
  ptraverse' = coerceDimap unPar1 Par1
  {-# INLINEABLE ptraverse' #-}

instance (Transparent c) => GPTraversable' (K1 i c) where
  ptraverse' _ = coerceDimap unK1 K1 $ describe

instance (GPTraversable' f) => GPTraversable' (M1 i c f) where
  ptraverse' = coerceDimap unM1 M1 . ptraverse'
  {-# INLINEABLE ptraverse' #-}

instance (PTraversable f) => GPTraversable' (Rec1 f) where
  ptraverse' = coerceDimap unRec1 Rec1 . ptraverse
  {-# INLINEABLE ptraverse' #-}

instance (GPTraversable' f, GPTraversable' g) => GPTraversable' (f :+: g) where
  ptraverse' p = dimap toE fromE $ ptraverse' p +++ ptraverse' p
    where
      toE (L1 fa) = Left fa
      toE (R1 ga) = Right ga
      fromE (Left fa) = L1 fa
      fromE (Right ga) = R1 ga
  {-# INLINEABLE ptraverse' #-}

instance (GPTraversable' f, GPTraversable' g) => GPTraversable' (f :*: g) where
  ptraverse' p = dimap toTup fromTup $ ptraverse' p *** ptraverse' p
    where
      toTup (fa :*: ga) = (fa, ga)
      fromTup (fa, ga) = fa :*: ga
  {-# INLINEABLE ptraverse' #-}

instance (PTraversable f, GPTraversable' g, Traversable g)
  => GPTraversable' (f :.: g) where
  ptraverse' = coerceDimap unComp1 Comp1 . ptraverse . ptraverse'
  {-# INLINEABLE ptraverse' #-}
