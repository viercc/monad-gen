{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.DoubleMonoid (
  DoubleMonoid(..),
) where

import Data.Monoid (Dual(..))

import qualified Data.DoubleMonoid.Free as DM
import Data.Ix (Ix)
import Data.Foldable (foldl')

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
-- **Note that** not even @zero \/*\/ x === zero@ is assumed!

class DoubleMonoid a where
  {-# MINIMAL one, (/*/), zero, (/+/) | mprod, msum | doubleMonoidAlgebra #-}

  -- | 'one' is the unit of @\/*\/@
  one :: a
  one = doubleMonoidAlgebra id DM.One

  -- | The operator @('/+/')@ form a monoid with 'zero' as its unit.
  --
  -- In other words, these \"monoid laws\" must hold.
  --
  -- @
  -- (x \/+\/ y) \/+\/ z === x \/+\/ (y \/+\/ z)
  -- zero \/+\/ x === x
  -- x \/+\/ zero === x
  -- @
  --
  (/*/) :: a -> a -> a
  x /*/ y = doubleMonoidAlgebra id (DM.Lit x DM.:/*/ DM.Lit y)

  -- | 'zero' is the unit of \"additive\" monoid.
  zero :: a
  zero = doubleMonoidAlgebra id DM.Zero

  -- | The binary operator @('/+/')@ of \"additive\" monoid.
  --
  (/+/) :: a -> a -> a
  x /+/ y = doubleMonoidAlgebra id (DM.Lit x DM.:/+/ DM.Lit y)
  
  -- | Fold a list using '/*/' monoid.
  mprod :: [a] -> a
  mprod = foldr (/*/) one
  
  -- | Fold a list using '/+/' monoid.
  msum :: [a] -> a
  msum = foldr (/+/) zero

  -- | A 'DoubleMonoid' is an algebra of 'DM.Free'
  -- 
  -- @
  -- doubleMonoidAlgebra f . join === doubleMonoidAlgebra (doubleMonoidAlgebra f)
  -- @
  doubleMonoidAlgebra :: (b -> a) -> DM.Free b -> a
  doubleMonoidAlgebra f = go
    where
      go (DM.Lit a) = f a
      go (DM.Sum xs) = case xs of
        [DM.Prod xs'] -> mprod (go <$> xs')
        _ -> msum (go <$> xs)

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

instance DoubleMonoid (DM.Free a) where
  mprod = DM.Prod
  msum = DM.Sum
  doubleMonoidAlgebra = (=<<)
