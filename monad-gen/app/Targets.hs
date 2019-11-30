{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Targets where

import GHC.Generics
import Data.PTraversable

data F a = F0 | F2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 F) instance PTraversable F

data G a = G1 a | G2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 G) instance PTraversable G

data H a = H0 | H1 a | H2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 H) instance PTraversable H

data W a = W1_0 a | W1_1 a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 W) instance PTraversable W

data T a = T2_0 a a | T2_1 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 T) instance PTraversable T

data J a = J1_0 a | J1_1 a | J2 a a
  deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 J) instance PTraversable J
