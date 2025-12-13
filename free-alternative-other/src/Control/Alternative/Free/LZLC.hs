{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}

-- | Free alternative (with /left zero/ + /left catch/).
--
-- 'Alternative' laws were not set to one, clear definition,
-- but there are two major ones.
--
-- For an instance of @(Alternative f)@, both laws have these in common.
--
-- - Inherited laws from 'Applicative'
-- - @('empty', '<|>')@ forms monoid on @f a@ for any type @a@.
-- - /Left zero/ law: @'empty' '<*>' x === 'empty'@.
--
-- Candidate #1 of the Alternative law have /Left distribution/ law.
--
-- @
-- -- Left distribution
-- (x '<|>' y) '<*>' z === (x \<*\> z) \<|\> (y \<*\> z)
-- @
--
-- Another candidate #2 have /Left catch/ law instead.
--
-- @
-- -- Left catch
-- 'pure' x '<|>' y === pure x
-- @
--
-- Reference Typeclassopedia <https://wiki.haskell.org/Typeclassopedia#Laws_6>
-- for more about these laws.
--
-- The \"free alternative\" construction for the alternative #1
-- (with /Left distribution/) is known and implemented.
--
-- - https://people.cs.kuleuven.be/~tom.schrijvers/Research/talks/ppdp2015.pdf
-- - <https://hackage.haskell.org/package/free-5.2/docs/Control-Alternative-Free.html>
--
-- This module provides the free alternative #2.
module Control.Alternative.Free.LZLC where

import Control.Applicative (Alternative (..))
import qualified Control.Applicative.Free.Zero as AZ

-- * Type definitions

-- | The Free (left zero + left catch) 'Alternative'.
data Free f a where
  Pure :: a -> Free f a
  Zero :: Free f a
  Lift :: f a -> Free f a
  SumOf :: Sz' (SummandF f) a -> Free f a
  ApOf :: Az' (FactorF f) a -> Free f a
  deriving (Functor)

data SummandF f a where
  SummandLift :: f a -> SummandF f a
  SummandAp :: Az' (FactorF f) a -> SummandF f a
  deriving (Functor)

data FactorF f a where
  FactorLift :: f a -> FactorF f a
  FactorSum :: Sz' (SummandF f) a -> FactorF f a
  deriving (Functor)

injectSummand :: SummandF f a -> Free f a
injectSummand (SummandLift fa) = Lift fa
injectSummand (SummandAp fas) = ApOf fas

injectFactor :: FactorF f a -> Free f a
injectFactor (FactorLift fa) = Lift fa
injectFactor (FactorSum fas) = SumOf fas

viewSum :: Free f a -> Sz (SummandF f) a
viewSum (Pure a) = Zee a
viewSum Zero = Nil
viewSum (Lift fa) = singletonSz (SummandLift fa)
viewSum (SumOf fas) = case fas of
  SzFz fa a -> Cons fa (Zee a)
  SzLong f1 f2 rest -> Cons f1 (Cons f2 rest)
viewSum (ApOf fas) = singletonSz (SummandAp fas)

viewAp :: Free f a -> Az (FactorF f) a
viewAp (Pure a) = AZ.Pure a
viewAp Zero = AZ.Zero
viewAp (Lift fa) = singletonAz (FactorLift fa)
viewAp (SumOf fas) = singletonAz (FactorSum fas)
viewAp (ApOf fas) = case fas of
  AzFz fa -> AZ.Ap fa AZ.Zero
  AzLong fa fb mk -> AZ.Ap fa (AZ.Ap fb mk)

instance (Functor f) => Applicative (Free f) where
  pure = Pure
  x <*> y = case viewAp x <*> viewAp y of
    AZ.Pure b -> Pure b
    AZ.Zero -> Zero
    AZ.Ap z (AZ.Pure k) -> injectFactor (k <$> z)
    AZ.Ap z AZ.Zero -> ApOf $ AzFz z
    AZ.Ap z1 (AZ.Ap z2 r) -> ApOf $ AzLong z1 z2 r

instance (Functor f) => Alternative (Free f) where
  empty = Zero
  x <|> y = case viewSum x <> viewSum y of
    Nil -> Zero
    Zee b -> Pure b
    Cons z Nil -> injectSummand z
    Cons z (Zee b) -> SumOf $ SzFz z b
    Cons z1 (Cons z2 r) -> SumOf $ SzLong z1 z2 r

-- * Auxiliary types

-- | Formal products of @f@ with zero.
type Az = AZ.Free

singletonAz :: f a -> Az f a
singletonAz fa = AZ.Ap fa (AZ.Pure id)

-- | Nontrivial products. Az but not @pure a@, @Zero@, nor @singletonAz fa@.
data Az' f a where
  AzFz :: f a -> Az' f b
  AzLong :: f a -> f b -> Az f (b -> a -> c) -> Az' f c

instance Functor (Az' f) where
  fmap _ (AzFz fa) = AzFz fa
  fmap f (AzLong fa fb rest) = AzLong fa fb (fmap (\k b a -> f (k b a)) rest)

-- | Formal sums of @f@ with absorbing elements.
--
-- > Nil  : Empty sum
-- > Cons : Append one summand (f a) to a sum
-- > Zee  : @pure@ which absorbs any summand right to it
data Sz f a = Nil | Zee a | Cons (f a) (Sz f a)
  deriving (Functor)

singletonSz :: f a -> Sz f a
singletonSz fa = Cons fa Nil

instance Semigroup (Sz f a) where
  Nil <> y = y
  Zee a <> _ = Zee a
  Cons x xs <> y = Cons x (xs <> y)

instance Monoid (Sz f a) where
  mempty = Nil

-- | Nontrivial sums. Sz but not @Nil@, @Zee a@, nor @singletonSz fa@.
data Sz' f a = SzFz (f a) a | SzLong (f a) (f a) (Sz f a)
  deriving (Functor)
