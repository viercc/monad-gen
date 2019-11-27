{-# LANGUAGE
  DeriveTraversable,
  FlexibleInstances,
  QuantifiedConstraints
#-}
module Internal.Util(
  coerceMap,
  coerceBimap,
  coerceDimap,
  Generically(..),
  Generically1(..),

  Representational1,
  Representational2
) where

import Data.Coerce

coerceMap :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
coerceMap _ = coerce
{-# INLINE coerceMap #-}

coerceBimap :: Coercible (f a b) (f a' b') => (a -> a') -> (b -> b') -> f a b -> f a' b'
coerceBimap _ _ = coerce
{-# INLINE coerceBimap #-}

coerceDimap :: Coercible (f a b) (f a' b') => (a' -> a) -> (b -> b') -> f a b -> f a' b'
coerceDimap _ _ = coerce
{-# INLINE coerceDimap #-}

newtype Generically x = Generically { unGenerically :: x }

newtype Generically1 f x = Generically1 { unGenerically1 :: f x }
  deriving (Functor, Foldable, Traversable)

class (forall x x'. (Coercible x x') => Coercible (f x) (f x'))
  => Representational1 f

instance (forall x x'. (Coercible x x') => Coercible (f x) (f x'))
  => Representational1 f

class (forall x y x' y'.
        (Coercible x x', Coercible y y') => Coercible (p x y) (p x' y'))
      => Representational2 p

instance (forall x y x' y'.
           (Coercible x x', Coercible y y') => Coercible (p x y) (p x' y'))
         => Representational2 p
