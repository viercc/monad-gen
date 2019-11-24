{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.IntRange.Unsafe(
  UpTo(..),
  getUpTo,
  makeUpTo,
  wholeRange,
  unsafeWrap,
) where

import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Functor.Const
import Data.Functor.Classes

import Data.Coerce
import Data.Reflection

newtype UpTo n = MkUpTo Int
  deriving (Show, Eq, Ord)
  deriving (Eq1, Ord1) via (Const Int)

type role UpTo nominal

getUpTo :: UpTo n -> Int
getUpTo = coerce

makeUpTo :: forall n. (Reifies n Int) => Int -> Maybe (UpTo n)
makeUpTo x | 0 <= x && x < nvalue = Just (MkUpTo x)
           | otherwise            = Nothing
  where nvalue = reflect @n Proxy

unsafeWrap :: forall n. (Reifies n Int) => Int -> UpTo n
unsafeWrap = fromMaybe oob . makeUpTo

wholeRange :: forall n. (Reifies n Int) => [UpTo n]
wholeRange = coerce [0 .. nvalue - 1]
  where nvalue = reflect @n Proxy

oob :: a
oob = error "UpTo: Out of bounds"

instance Reifies n Int => Enum (UpTo n) where
  toEnum = unsafeWrap
  fromEnum = coerce
  succ = toEnum . succ . fromEnum
  pred = toEnum . pred . fromEnum
  enumFrom (MkUpTo x) = coerce $ enumFromTo x (nvalue-1)
    where nvalue = max 0 (reflect @n Proxy)
  enumFromThen (MkUpTo x) (MkUpTo x') =
    coerce $ enumFromThenTo x x' (nvalue-1)
    where nvalue = max 0 (reflect @n Proxy)
  enumFromThenTo = coerce (enumFromThenTo @Int)

instance Reifies n Int => Bounded (UpTo n) where
  maxBound | nvalue > 0 = MkUpTo (nvalue - 1)
           | otherwise  = oob
    where nvalue = reflect @n Proxy
  minBound | nvalue > 0 = MkUpTo 0
           | otherwise  = oob
    where nvalue = reflect @n Proxy
