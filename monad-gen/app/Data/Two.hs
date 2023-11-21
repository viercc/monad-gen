{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
module Data.Two where

import Data.Transparent
import Data.Bits (Bits(..))
import Text.Read (Read(readPrec))

newtype Two = Two Bool
  deriving stock (Eq, Ord)
  deriving newtype (Bits, Transparent)

instance Num Two where
  fromInteger = Two . odd
  (+) = xor
  (*) = (.&.)
  negate = id
  abs = id
  signum = id

instance Show Two where
  show (Two b) = if b then "1" else "0"

instance Read Two where
  readPrec = fromInteger <$> readPrec
