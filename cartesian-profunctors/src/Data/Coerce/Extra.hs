{-# LANGUAGE
  DeriveTraversable,
  FlexibleInstances,
  QuantifiedConstraints
#-}
module Data.Coerce.Extra(
  Representational1,
  Representational2,
  coerceMap,
  coerceBimap,
  coerceDimap
) where

import Data.Coerce

class (forall a a'. Coercible a a' => Coercible (f a) (f a'))
  => Representational1 f
instance (forall a a'. Coercible a a' => Coercible (f a) (f a'))
  => Representational1 f

class (forall a a' b b'.
         (Coercible a a', Coercible b b') => Coercible (f a b) (f a' b'))
  => Representational2 f
instance (forall a a' b b'.
  (Coercible a a', Coercible b b') => Coercible (f a b) (f a' b'))
  => Representational2 f

coerceMap :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
coerceMap _ = coerce
{-# INLINE coerceMap #-}

coerceBimap :: Coercible (f a b) (f a' b') => (a -> a') -> (b -> b') -> f a b -> f a' b'
coerceBimap _ _ = coerce
{-# INLINE coerceBimap #-}

coerceDimap :: Coercible (f a b) (f a' b') => (a' -> a) -> (b -> b') -> f a b -> f a' b'
coerceDimap _ _ = coerce
{-# INLINE coerceDimap #-}
