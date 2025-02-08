{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
module Data.Two where

import Data.Bits (Bits(..))
import Text.Read (Read(readPrec))
import Data.Finitary.Enum qualified as Fin

newtype Two = Two Bool
  deriving stock (Eq, Ord)
  deriving newtype (Bits, Fin.Enum)

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

data N3 = N3_0 | N3_1 | N3_2
  deriving stock (Eq, Ord, Enum, Bounded)

instance Fin.Enum N3 where
  withEnum k = k @3 to from
    where
      to N3_0 = 0
      to N3_1 = 1
      to N3_2 = 2
      from 0 = N3_0
      from 1 = N3_1
      from _ = N3_2

instance Num N3 where
  fromInteger n = toEnum (fromInteger (n `mod` 3))
  
  x + y = toEnum ((fromEnum x + fromEnum y) `mod` 3)
  x - y = toEnum ((fromEnum x - fromEnum y) `mod` 3)
  x * y = toEnum ((fromEnum x * fromEnum y) `mod` 3)

  abs = id
  signum x = if x == 0 then 0 else 1

instance Show N3 where
  show = show . fromEnum

instance Read N3 where
  readPrec = fromInteger <$> readPrec

