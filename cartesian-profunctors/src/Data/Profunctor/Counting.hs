{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE DeriveTraversable #-}
module Data.Profunctor.Counting(
  Counting(..)
) where

import Data.Functor.Classes
import Control.Applicative
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

import Data.Profunctor
import Data.Profunctor.Cartesian

import Data.Coerce

newtype Counting a b = Counting { getCounting :: Int }
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Eq1, Ord1, Contravariant)
           via (Const Int)

instance Profunctor Counting where
  dimap _ _ = coerce
  lmap _ = coerce
  rmap _ = coerce

instance Cartesian Counting where
  proUnit = Counting 1
  Counting a *** Counting b = Counting (a * b)

instance Cocartesian Counting where
  proEmpty = Counting 0
  Counting a +++ Counting b = Counting (a + b)

instance Applicative (Counting x) where
  pure _ = Counting 1
  Counting a <*> Counting b = Counting (a * b)

instance Alternative (Counting x) where
  empty = Counting 0
  Counting a <|> Counting b = Counting (a + b)

instance Divisible (Counting x) where
  conquer = Counting 1
  divide _ (Counting a) (Counting b) = Counting (a * b)

instance Decidable (Counting x) where
  lose _ = Counting 0
  choose _ (Counting a) (Counting b) = Counting (a + b)
