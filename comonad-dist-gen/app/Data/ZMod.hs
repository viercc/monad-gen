{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.ZMod where

import Data.Coerce (coerce)
import Data.Bool (bool)

import Data.Finite
import Data.Finitary

import GHC.TypeNats (Nat, KnownNat)

import Data.Group
import Util.WrappedIntegral
import Data.Monoid (Sum(..))
import Data.Semigroup (Semigroup(..))

newtype ZMod (n :: Nat) = ZMod { unZMod :: Finite n }
  deriving (Eq, Ord, Enum, Bounded, Finitary, Real, Integral) via (Finite n)
  deriving (Show, Read) via (WrappedIntegral (ZMod n))
  deriving (Semigroup, Monoid, Group) via (Sum (ZMod n))

-- | Num operations of @'Finite' n@ are modular arithmetics,
--   but @fromInteger@ is not 'modulo'.
instance KnownNat n => Num (ZMod n) where
  fromInteger = ZMod . modulo

  ZMod x + ZMod y = ZMod (x + y)
  ZMod x - ZMod y = ZMod (x - y)
  ZMod x * ZMod y = ZMod (x * y)
  abs = id
  signum x
    | x == 0 = 0
    | otherwise = 1

--

-- | Bit = {0,1} with modular arithmetics
newtype Bit = Bit Bool
  deriving (Eq, Ord, Enum, Bounded, Finitary) via Bool
  deriving (Show, Read) via (WrappedIntegral Bit)

xor :: Bool -> Bool -> Bool
xor = (/=)

instance Num Bit where
  fromInteger = Bit . odd
  (+) = coerce xor
  (-) = coerce xor
  (*) = coerce (&&)
  abs = id
  signum = id

instance Real Bit where
  toRational (Bit b) = bool 0 1 b

instance Integral Bit where
  toInteger (Bit b) = bool 0 1 b
  quotRem x (Bit d) = if d then (x,0) else error "division by zero"

instance Semigroup Bit where
  (<>) = (+)
  stimes n b = b * fromInteger (toInteger n)

instance Monoid Bit where
  mempty = 0

instance Group Bit where
  pow = flip stimes
  invert = id
  (~~) = (+)