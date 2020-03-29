{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Newtypes(
    WrappedIntegral(..)
  , Two(..)
  , Three(..)
) where

import Text.Read(Read(..))
import Data.Functor.Identity
import Data.Profunctor

import GHC.Generics (Generic, Generic1)

import Data.Profunctor.Cartesian
import Data.Transparent
import Data.PTraversable

newtype WrappedIntegral a =
  WrapIntegral { unWrapIntegral :: a }
  deriving stock (Functor, Foldable, Traversable, Generic, Generic1)
  deriving (Applicative, Monad) via Identity
  deriving (Eq, Ord, Enum, Bounded, Num, Real, Integral) via a

instance Transparent a => Transparent (WrappedIntegral a) where
  describe = dimap unWrapIntegral WrapIntegral describe

instance PTraversable WrappedIntegral where
  ptraverse = dimap unWrapIntegral WrapIntegral

instance Integral a => Show (WrappedIntegral a) where
  show = show . toInteger

instance Num a => Read (WrappedIntegral a) where
  readPrec = fromInteger <$> readPrec



newtype Two = Two Bool
  deriving stock (Eq, Ord)
  deriving (Enum, Bounded) via Bool
  deriving (Show, Read) via (WrappedIntegral Two)

instance Transparent Two where
  describe = dimap (\(Two b) -> b) Two describe

instance Num Two where
  fromInteger n = Two (odd n)
  Two a + Two b = Two (a /= b)
  negate = id
  abs = id
  signum = id
  Two a * Two b = Two (a && b)

instance Real Two where
  toRational = toRational . toInteger

instance Integral Two where
  toInteger (Two b) = if b then 1 else 0
  quotRem = quotRemDefault

data Three = N3_0 | N3_1 | N3_2
  deriving stock (Eq, Ord, Enum, Bounded)
  deriving (Show, Read) via (WrappedIntegral Three)

instance Num Three where
  fromInteger n = case n `mod` 3 of
    0 -> N3_0
    1 -> N3_1
    _ -> N3_2

  x + y = fromInteger (toInteger x + toInteger y)
  x - y = fromInteger (toInteger x - toInteger y)
  x * y = fromInteger (toInteger x * toInteger y)
  
  negate = fromInteger . negate . toInteger
  
  abs = id
    
  signum 0 = 0
  signum _ = 1

instance Real Three where
  toRational = toRational . toInteger

instance Integral Three where
  toInteger N3_0 = 0
  toInteger N3_1 = 1
  toInteger N3_2 = 2

  quotRem = quotRemDefault

instance Transparent Three where
  describe = dimap l r $ proUnit +++ (proUnit +++ proUnit)
    where
      l N3_0 = Left ()
      l N3_1 = Right (Left ())
      l N3_2 = Right (Right ())
      
      r (Left _) = N3_0
      r (Right (Left _)) = N3_1
      r (Right (Right _)) = N3_2

-----------

quotRemDefault :: (Integral a) => a -> a -> (a, a)
quotRemDefault a b =
  let (q,r) = quotRem (toInteger a) (toInteger b)
  in (fromInteger q, fromInteger r)
