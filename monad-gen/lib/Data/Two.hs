{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
module Data.Two where

import Data.Transparent
import Data.Bits (Bits(..))
import Text.Read (Read(readPrec))
import Data.Profunctor.Cartesian
import Data.Profunctor (Profunctor(..))

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

data N3 = N3_0 | N3_1 | N3_2
  deriving stock (Eq, Ord, Enum, Bounded)

instance Transparent N3 where
  describeOn f g = dimap (to . f) (g . from) (proUnit +++ proUnit +++ proUnit)
    where
      k = const
      from = either (either (k N3_0) (k N3_1)) (k N3_2)
      to N3_0 = Left (Left ())
      to N3_1 = Left (Right ())
      to N3_2 = Right ()

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

