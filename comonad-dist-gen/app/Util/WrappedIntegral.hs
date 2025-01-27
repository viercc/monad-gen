{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Util.WrappedIntegral(
    WrappedIntegral(..),
    quotRemDefault
) where

import Text.Read(Read(..))
import Data.Functor.Identity

import GHC.Generics (Generic, Generic1)

newtype WrappedIntegral a =
  WrapIntegral { unWrapIntegral :: a }
  deriving stock (Functor, Foldable, Traversable, Generic, Generic1)
  deriving (Applicative, Monad) via Identity
  deriving (Eq, Ord, Enum, Bounded, Num, Real, Integral) via a

instance Integral a => Show (WrappedIntegral a) where
  show = show . toInteger

instance Num a => Read (WrappedIntegral a) where
  readPrec = fromInteger <$> readPrec

-----------

quotRemDefault :: (Integral a) => a -> a -> (a, a)
quotRemDefault a b =
  let (q,r) = quotRem (toInteger a) (toInteger b)
  in (fromInteger q, fromInteger r)
