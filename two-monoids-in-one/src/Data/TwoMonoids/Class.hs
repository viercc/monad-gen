{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

module Data.TwoMonoids.Class
  ( TwoMonoids (..),
    one,
    mprod,
    mpow,
  )
where

import Control.Applicative (Alternative (..), (<|>))
import Data.Coerce (Coercible, coerce)
import Data.Ix (Ix)
import Data.Monoid (Ap)
import Data.Semigroup
import Numeric.Natural (Natural)

-- | @TwoMonoids@ is a @Monoid@ with another additional monoid structure.
--
-- The additional monoid is called the \"additive\" monoid and operators are named additively @('zero', '\<+\>')@.
-- The original monoid is referred as \"multiplicative\" monoid.
--
-- Contrary to what the names suggest,
-- @TwoMonoids@ do not impose laws about relation between the two
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
-- Near-semiring is a subclass of TwoMonoids
-- which additionally satisfy \"left distribution law\" (which confusingly have
-- another name \"right distributivity\").
--
-- @
-- -- in near-semiring
-- zero <> x  === zero
-- (x \<+\> y) <> z === (x <> z) \<+\> (y <> z)
-- @
class (Monoid a) => TwoMonoids a where
  {-# MINIMAL zero, (<+>) | msum #-}

  -- | The unit of \"additive\" monoid.
  zero :: a
  zero = msum []

  -- | The binary operator of \"additive\" monoid.
  (<+>) :: a -> a -> a
  x <+> y = msum [x, y]

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
one :: (TwoMonoids a) => a
one = mempty

-- | Synonym of 'mconcat' but renamed to emphasize it is for \"multiplicative\" monoid.
mprod :: (TwoMonoids a) => [a] -> a
mprod = mconcat

-- | Type-restricted synonym of 'mtimesDefault' but renamed to emphasize it is for \"multiplicative\" monoid.
mpow :: (TwoMonoids a) => Natural -> a -> a
mpow = mtimesDefault

deriving newtype instance (TwoMonoids a) => TwoMonoids (Dual a)

-- | Make a @TwoMonoids@ by specifying two monoid
--   sharing the same runtime representation ('Coercible').
--
--   The first and the second arguments specify \"multiplicative\" and \"additive\"
--   monoids in this order.
newtype TwoMonoidsVia m a = TwoMonoidsVia m
  deriving newtype (Semigroup, Monoid)

instance (Monoid m, Coercible m a, Monoid a) => TwoMonoids (TwoMonoidsVia m a) where
  zero = coerce (mempty @a)
  (<+>) = coerce (mappend @a)
  mtimes n = coerce (mtimesDefault @Natural @a n)

-- | Turn a @TwoMonoids@ to the usual @Monoid@ of the additive monoid,
--   forgetting multiplicative one.
--
--   (Note: you don't need @Multiplicative@ newtype wrapper, as
--   the @TwoMonoids@ class inherits its multiplication from its superclass @Monoid@.)
newtype Additive m = Additive {getAdditive :: m}

instance (TwoMonoids m) => Semigroup (Additive m) where
  (<>) = coerce ((<+>) @m)
  stimes n
    | n < 0 = error "negative exponent"
    | otherwise = coerce (mtimes @m (fromIntegral n))

instance (TwoMonoids m) => Monoid (Additive m) where
  mempty = coerce (zero @m)

-- | @AsNum a ≅ TwoMonoidsVia (Product a) (Sum a)@
newtype AsNum a = AsNum a
  deriving stock (Eq, Ord)
  deriving newtype
    ( Show,
      Read,
      Enum,
      Bounded,
      Ix,
      Num,
      Real,
      Integral
    )
  deriving (Semigroup, Monoid, TwoMonoids) via (TwoMonoidsVia (Product a) (Sum a))

-- | Trivial
instance TwoMonoids () where
  msum _ = ()
  mtimes _ _ = ()

-- | Direct product
instance (TwoMonoids a, TwoMonoids b) => TwoMonoids (a, b) where
  msum xys = let (xs, ys) = unzip xys in (msum xs, msum ys)
  mtimes n (x, y) = (mtimes n x, mtimes n y)

-- | > one = pure mempty; (<>) = liftA2 (<>); zero = empty; ('<+>') = ('<|>')
instance (Alternative f, Monoid a) => TwoMonoids (Ap f a) where
  zero = empty
  (<+>) = (<|>)
