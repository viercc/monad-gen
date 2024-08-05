{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.DoubleMonoid.Class (
  DoubleMonoid(..),
) where

import Data.Monoid (Dual(..))

import Data.Ix (Ix)
import Data.Foldable (foldl')
import Control.Applicative ((<|>))

-- | @DoubleMonoid@ is a type with two independent monoid structures.
--
-- The two monoids are named \"additive\" @(zero, \/+\/)@ and
-- \"multiplicative\" @(one, \/*\/)@ respectively. But unlike 'Num' or
-- (semi)ring structures, @DoubleMonoid@ assume no relation between the two
-- monoids like distributivity.
-- 
-- ==== Laws
--
-- Monoid laws of \"additive\" set of operators:
--
-- @
-- (x \/+\/ y) \/+\/ z === x \/+\/ (y \/+\/ z)
-- zero \/+\/ x === x
-- x \/+\/ zero === x
-- @
--
-- Monoid laws of \"multiplicative\" set of operators:
--
-- @
-- (x \/*\/ y) \/*\/ z === x \/*\/ (y \/*\/ z)
-- one \/*\/ x === x
-- x \/*\/ one === x
-- @
-- 
-- ==== Relation to other known algebraic structures
-- 
-- Of course, @DoubleMonoid@ can be seen as @Monoid@ in two ways.
-- Other than that, near-semiring (TODO:url) is a subclass of DoubleMonoid
-- which additionally satisfy \"left distribution law\" (which confusingly have
-- another name \"right distributivity\").
--
-- @
-- -- in near-semiring
-- zero \/*\/ x  === zero
-- (x \/+\/ y) \/*\/ z === (x \/*\/ z) \/+\/ (y \/*\/ z)
-- @

class DoubleMonoid a where
  {-# MINIMAL one, (/*/), zero, (/+/) | mprod, msum #-}

  -- | The unit of \"multiplicative\" monoid.
  one :: a
  one = mprod []

  -- | The binary operator of \"multiplicative\" monoid.
  (/*/) :: a -> a -> a
  x /*/ y = mprod [x,y]

  -- | The unit of \"additive\" monoid.
  zero :: a
  zero = msum []

  -- | The binary operator of \"additive\" monoid.
  (/+/) :: a -> a -> a
  x /+/ y = msum [x,y]
  
  -- | Fold a list using '/*/' monoid.
  mprod :: [a] -> a
  mprod = foldr (/*/) one
  
  -- | Fold a list using '/+/' monoid.
  msum :: [a] -> a
  msum = foldr (/+/) zero

infixr 5 /+/

infixr 6 /*/

deriving newtype instance DoubleMonoid a => DoubleMonoid (Dual a)

-- | Use the usual '(+)' and '(*)' operators of 'Num' class
--   as DoubleMonoid 
newtype AsNum a = AsNum a
  deriving stock (Eq, Ord)
  deriving newtype
    (Show, Read,
     Enum, Bounded, Ix,
     Num, Real, Integral)

instance Num a => DoubleMonoid (AsNum a) where
  zero = 0
  (/+/) = (+)
  one = 1
  (/*/) = (*)

  msum = foldl' (+) 0
  mprod = foldl' (*) 1

-- | Trivial
instance DoubleMonoid () where
  msum _ = ()
  mprod _ = ()

-- | Product
instance (DoubleMonoid a, DoubleMonoid b) => DoubleMonoid (a,b) where
  msum xys = let (xs, ys) = unzip xys in (msum xs, msum ys)
  mprod xys = let (xs, ys) = unzip xys in (mprod xs, mprod ys)

-- | @('/+/') = ('<|>'); ('/*/') = liftA2 ('<>')@
instance Monoid a => DoubleMonoid (Maybe a) where
  zero = Nothing
  one = Just mempty
  (/+/) = (<|>)
  (/*/) = liftA2 (<>)

-- | @('/+/') = ('++'); ('/*/') = liftA2 ('<>')@
instance Monoid a => DoubleMonoid [a] where
  zero = []
  one = [mempty]
  (/+/) = (<|>)
  (/*/) = liftA2 (<>)
