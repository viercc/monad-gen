{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Targets where

import Data.Bool (bool)
import GHC.Generics
import Data.Profunctor
import Data.PTraversable
import Data.Transparent

data Two = A | B
  deriving stock (Show, Eq, Ord)

instance Transparent Two where
  describeOn f g = dimap ((B ==) . f) (g . bool A B) describe

data F a = F0 | F2 a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 F) instance PTraversable F

data G a = G1 a | G2 a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 G) instance PTraversable G

data G' a = G2' a a | G3' a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 G') instance PTraversable G'

data H a = H0 | H1 a | H2 a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 H) instance PTraversable H

data W a = W1 Two a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 W) instance PTraversable W

data J a = J1 Two a | J2 a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 J) instance PTraversable J

data T a = T2 Two a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 T) instance PTraversable T

data Y a = Y0 | Y1 Two Two a | Y3 a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 Y) instance PTraversable Y
