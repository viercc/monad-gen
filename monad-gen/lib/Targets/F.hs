module Targets.F where

data F_0_2 a = Fa0 | Fa2 a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 F)

data F_0_1_2 a = Fb0 | Fb1 a | Fb2 a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 H)

data I' a = Iz | I1 a | I3 a a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 I')

data K a = K | K' | Ka a | Kb a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 K)

data V a = V | Va a | Vb a | Vc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 V)

data X a = X | X' | Xa a | Xb a | Xab a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 X)

data Y a = Y | Yaa a | Yab a | Yba a | Ybb a | Yc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
  deriving (Eq1, Ord1, PTraversable) via (Generically1 Y)
