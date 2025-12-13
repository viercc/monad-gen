{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeApplications #-}
module Data.DoubleMonoid.Class (
  DoubleMonoid(..),
  one, mprod, mpow
) where

import Data.Ix (Ix)
import Control.Applicative ((<|>), Alternative (..))
import Numeric.Natural (Natural)
import Data.Semigroup
import Data.Coerce (Coercible, coerce)
import Data.Monoid (Ap)

-- | @DoubleMonoid@ is a @Monoid@ with another additional monoid structure.
--
-- The additional monoid is called the \"additive\" monoid and operators are named additively @('zero', '\<+\>')@.
-- The original monoid is referred as \"multiplicative\" monoid.
-- 
-- Contrary to what the names suggest,
-- @DoubleMonoid@ do not impose laws about relation between the two
-- monoids like distributivity (like @Num@ do.)
-- 
-- ==== Laws
--
-- Monoid laws of \"additive\" set of operators:
--
-- @
-- (x \<+\> y) \<+\> z === x \<+\> (y \<+\> z)
-- zero \<+\> x === x
-- x \<+\> zero === x
-- @
-- 
-- ==== Relation to other known algebraic structures
-- 
-- Near-semiring is a subclass of DoubleMonoid
-- which additionally satisfy \"left distribution law\" (which confusingly have
-- another name \"right distributivity\").
--
-- @
-- -- in near-semiring
-- zero <> x  === zero
-- (x \<+\> y) <> z === (x <> z) \<+\> (y <> z)
-- @

class Monoid a => DoubleMonoid a where
  {-# MINIMAL zero, (<+>) | msum #-}

  -- | The unit of \"additive\" monoid.
  zero :: a
  zero = msum []

  -- | The binary operator of \"additive\" monoid.
  (<+>) :: a -> a -> a
  x <+> y = msum [x,y]
  
  -- | Fold a list using '<+>' monoid.
  msum :: [a] -> a
  msum = foldr (<+>) zero

  -- | @n@-fold repeated addition.
  --
  -- Beware that 'stimes' from @Data.Semigroup@ module is for
  -- the \"multiplicative\" monoid and different to 'mtimes'.
  mtimes :: Natural -> a -> a
  mtimes n = getAdditive . stimesMonoid n . Additive

infixr 5 <+>

-- | Synonym of 'mempty' but renamed to emphasize it is for \"multiplicative\" monoid.
one :: DoubleMonoid a => a
one = mempty

-- | Synonym of 'mconcat' but renamed to emphasize it is for \"multiplicative\" monoid.
mprod :: DoubleMonoid a => [a] -> a
mprod = mconcat

-- | Type-restricted synonym of 'mtimesDefault' but renamed to emphasize it is for \"multiplicative\" monoid.
mpow :: (DoubleMonoid a) => Natural -> a -> a
mpow = mtimesDefault

deriving newtype instance DoubleMonoid a => DoubleMonoid (Dual a)

-- | Make a @DoubleMonoid@ by specifying two monoid
--   sharing the same runtime representation ('Coercible').
--
--   The first and the second arguments specify \"multiplicative\" and \"additive\"
--   monoids in this order.
newtype DoubleMonoidVia m a = DoubleMonoidVia m
  deriving newtype (Semigroup, Monoid)

instance (Monoid m, Coercible m a, Monoid a) => DoubleMonoid (DoubleMonoidVia m a) where
  zero = coerce (mempty @a)
  (<+>) = coerce (mappend @a)
  mtimes n = coerce (mtimesDefault @Natural @a n)

-- | Turn a @DoubleMonoid@ to the usual @Monoid@ of the additive monoid,
--   forgetting multiplicative one.
--
--   (Note: you don't need @Multiplicative@ newtype wrapper, as
--   the @DoubleMonoid@ class inherits its multiplication from its superclass @Monoid@.)
newtype Additive m = Additive { getAdditive :: m }

instance (DoubleMonoid m) => Semigroup (Additive m) where
  (<>) = coerce ((<+>) @m)
  stimes n
    | n < 0 = error "negative exponent"
    | otherwise = coerce (mtimes @m (fromIntegral n)) 

instance (DoubleMonoid m) => Monoid (Additive m) where
  mempty = coerce (zero @m)

-- | @AsNum a ≅ DoubleMonoidVia (Product a) (Sum a)@
newtype AsNum a = AsNum a
  deriving stock (Eq, Ord)
  deriving newtype
    (Show, Read,
     Enum, Bounded, Ix,
     Num, Real, Integral)
  deriving (Semigroup, Monoid, DoubleMonoid) via (DoubleMonoidVia (Product a) (Sum a))

-- | Trivial
instance DoubleMonoid () where
  msum _ = ()
  mtimes _ _ = ()

-- | Direct product
instance (DoubleMonoid a, DoubleMonoid b) => DoubleMonoid (a,b) where
  msum xys = let (xs, ys) = unzip xys in (msum xs, msum ys)
  mtimes n (x,y) = (mtimes n x, mtimes n y)

-- | > one = pure mempty; (<>) = liftA2 (<>); zero = empty; ('<+>') = ('<|>')
instance (Alternative f, Monoid a) => DoubleMonoid (Ap f a) where
  zero = empty
  (<+>) = (<|>)
