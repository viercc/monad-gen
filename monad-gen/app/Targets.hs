{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Targets where

import GHC.Generics
import Data.PTraversable

import Data.Two

data F a = F | Fa a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 F) instance PTraversable F

data G a = Ga a | Gb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 G) instance PTraversable G

data H a = H | Ha a | Hb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 H) instance PTraversable H

data I a = Ia a | Ib a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 I) instance PTraversable I

data J a = Ja a | Jb a | Jc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 J) instance PTraversable J

data T a = Ta a a | Tb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 T) instance PTraversable T

data U a = Ua a a | Ub a a | Uc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 U) instance PTraversable U

data Y a = Y | Ya Two Two a | Yb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 Y) instance PTraversable Y
