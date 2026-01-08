{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module Targets where

import GHC.Generics
import Data.Functor.Classes (Eq1, Ord1)
import Data.PTraversable

data F a = F | Fa a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 F)

data G a = Ga a | Gb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 G)

data H a = H | Ha a | Hb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 H)

data I a = Ia a | Ib a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 I)

data I' a = Iz | I1 a | I3 a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 I')

data J a = Ja a | Jb a | Jc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 J)

data K a = K | K' | Ka a | Kb a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 K)

data L a = La a a a | Lb a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 L)

data T a = Ta a a | Tb a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 T)

data U a = Ua a a | Ub a a | Uc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 U)

data W a = Wa a a | Wb a a | Wc a a | Wd a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 W)

data V a = V | Va a | Vb a | Vc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 V)

data X a = X | X' | Xa a | Xb a | Xab a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 X)

data Y a = Y | Yaa a | Yab a | Yba a | Ybb a | Yc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 Y)
