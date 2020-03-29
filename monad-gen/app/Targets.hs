{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Targets where

import GHC.Generics
import Data.PTraversable

import Newtypes

data F a = F0 | F2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 F) instance PTraversable F

data G a = G1 a | G2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 G) instance PTraversable G

data H a = H0 | H1 a | H2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 H) instance PTraversable H

data W a = W1 Two a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 W) instance PTraversable W

data J a = J1 Two a | J2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 J) instance PTraversable J

data T a = T2 Two a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 T) instance PTraversable T

data Y a = Y0 | Y2 a a | Y3 a a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 Y) instance PTraversable Y
