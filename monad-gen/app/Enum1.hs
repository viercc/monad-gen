{-# LANGUAGE
  ScopedTypeVariables,
  TypeApplications,
  AllowAmbiguousTypes,
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
module Enum1(
  Enum1(..),
  foldMapWithEnum1,
  lengthWithEnum1,
  Generically1(..),
  GEnum1'()
) where

import GHC.Generics
import Data.Functor.Identity

import Data.Coerce

import Data.Monoid(Sum(..))
import Control.Applicative
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

import Data.Functor.Counting

import Util
import Data.Functor.Contravariant.CoNumbering

{-
-- I want this but it seems not supported at the moment
type Representational f =
  forall x y. Coercible x y => Coercible (f x) (f y)
-}

class Enum1 t where
  enum1 :: (forall x y. Coercible x y => Coercible (f x) (f y), Alternative f)
        => f a -> f (t a)
  coenum1 :: (forall x y. Coercible x y => Coercible (f x) (f y), Decidable f)
          => f a -> f (t a)
  
  size1 :: Int -> Int
  size1 n = coerce $ enum1 @t (Counting n)
  
  fromEnum1 :: Int -> (a -> Int) -> t a -> Int
  fromEnum1 n f = getIndex $ coenum1 (ToN n f)

foldMapWithEnum1 :: forall t a m. (Enum1 t, Monoid m) => (a -> m) -> t a -> m
foldMapWithEnum1 f = coerce $ coenum1 @t (Op f)

lengthWithEnum1 :: (Enum1 t) => t a -> Int
lengthWithEnum1 = getSum . foldMapWithEnum1 (const 1)

newtype Generically1 f x = Generically1 { unGenerically1 :: f x }
  deriving (Functor, Foldable, Traversable)

instance (Generic1 t, GEnum1' (Rep1 t))
         => Enum1 (Generically1 t) where
  enum1 xs = Generically1 . to1 <$> enum1' xs
  coenum1 sx = contramap (from1 . unGenerically1) (coenum1' sx)
  {-# INLINEABLE enum1 #-}
  {-# INLINEABLE coenum1 #-}

deriving via (Generically1 Identity) instance Enum1 Identity
deriving via (Generically1 Maybe) instance Enum1 Maybe

instance (Enum1 f, Enum1 g) => Enum1 (f :.: g) where
  enum1 xs = coerceMap Comp1 $ enum1 (enum1 xs)
  coenum1 sx = coerceMap Comp1 $ coenum1 (coenum1 sx)
  {-# INLINEABLE enum1 #-}
  {-# INLINEABLE coenum1 #-}

-------------------------------------
-- Generics

class GEnum1' t where
  enum1' :: (forall x y. Coercible x y => Coercible (f x) (f y), Alternative f)
         => f a -> f (t a)
  coenum1' :: (forall x y. Coercible x y => Coercible (f x) (f y), Decidable f)
         => f a -> f (t a)

instance GEnum1' V1 where
  enum1' _ = empty
  coenum1' _ = lose (\v -> case v of { })
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}

instance GEnum1' U1 where
  enum1' _ = pure U1
  coenum1' _ = conquer
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}

instance GEnum1' Par1 where
  enum1' xs = coerceMap Par1 xs
  coenum1' sx = coerceMap Par1 sx
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}

instance (GEnum1' f) => GEnum1' (M1 i c f) where
  enum1' xs = coerceMap M1 $ enum1' @f xs
  coenum1' sx = coerceMap M1 $ coenum1' sx
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}

instance (Enum1 f) => GEnum1' (Rec1 f) where
  enum1' xs = coerceMap Rec1 $ enum1 @f xs
  coenum1' sx = coerceMap Rec1 $ coenum1 @f sx
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}

instance (GEnum1' f, GEnum1' g) => GEnum1' (f :+: g) where
  enum1' xs = (L1 <$> enum1' xs) <|> (R1 <$> enum1' xs)
  coenum1' sx = choose toEither (coenum1' sx) (coenum1' sx)
    where
      toEither (L1 fx) = Left fx
      toEither (R1 gx) = Right gx
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}

instance (GEnum1' f, GEnum1' g) => GEnum1' (f :*: g) where
  enum1' xs = (:*:) <$> enum1' xs <*> enum1' xs
  coenum1' sx = divide toTup (coenum1' sx) (coenum1' sx)
    where toTup (fx :*: gx) = (fx, gx)
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}

instance (Enum1 f, GEnum1' g) => GEnum1' (f :.: g) where
  enum1' xs = coerceMap Comp1 $ enum1 (enum1' xs)
  coenum1' sx = coerceMap Comp1 $ coenum1 (coenum1' sx)
  {-# INLINEABLE enum1' #-}
  {-# INLINEABLE coenum1' #-}
