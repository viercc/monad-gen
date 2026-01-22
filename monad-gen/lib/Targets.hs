{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Targets where

import GHC.Generics
import Data.Functor.Classes (Eq1, Ord1)
import Data.PTraversable

-- | F = T_02
data F a = F | Fa a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 F)

-- | G = T_12
data G a = Ga a | Gb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 G)

-- | H = T_012
data H a = H | Ha a | Hb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 H)

-- | I = T_13
data I a = Ia a | Ib a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 I)

-- * Complex functors

data T_013 a = T_013 | T_013_a a | T_013_b a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 T_013)

data T_112 a = T_112_a a | T_112_b a | T_112_c a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 T_112)

-- * Composite

-- | EW e w ~ Either e :.: Writer w ~ WriterT w (Either e)
data EW e w a = E e | W w a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 (EW e w))

-- | Reader (Fin 2)
data V2 a = V2 a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 V2)

-- | Reader (Fin 3)
data V3 a = V3 a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 V3)

-- | Update (or statelike) when v ~ Reader n
data St m v a = St m (v a)
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 (St m v))
