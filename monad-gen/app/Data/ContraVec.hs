{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.ContraVec(
  ToN(),
  
  genFromEnum,
  range,
  getIndex
) where

import Data.Void (absurd)

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

data ToN a = ToN !Int (a -> Int)

genFromEnum :: (Enum a) => a -> a -> ToN a
genFromEnum lo hi =
  let loKey = fromEnum lo
      hiKey = fromEnum hi
      len = hiKey - loKey + 1
  in ToN len (\a -> fromEnum a - loKey)

range :: ToN a -> Int
range (ToN n _) = n

getIndex :: ToN a -> a -> Int
getIndex (ToN _ f) a = f a

instance Contravariant ToN where
  contramap f (ToN n g) = ToN n (g . f)

instance Divisible ToN where
  divide p (ToN n f) (ToN m g) = ToN (n*m) h
    where
      h c = case p c of
        (a, b) -> m * f a + g b
  conquer = ToN 1 (const 0)

instance Decidable ToN where
  choose p (ToN n f) (ToN m g) = ToN (n+m) h
    where
      h c = case p c of
        Left a  -> f a
        Right b -> n + g b
  lose f = ToN 0 (absurd . f)
