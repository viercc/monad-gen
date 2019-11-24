{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE DeriveTraversable #-}
module Data.Functor.Counting(
  Counting(..)
) where

import Data.Functor.Classes
import Control.Applicative
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

newtype Counting x = Counting { getCounting :: Int }
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show1, Read1, Eq1, Ord1,
            Contravariant)
           via (Const Int)

instance Applicative Counting where
  pure _ = Counting 1
  Counting a <*> Counting b = Counting (a * b)

instance Alternative Counting where
  empty = Counting 0
  Counting a <|> Counting b = Counting (a + b)

instance Divisible Counting where
  divide _ (Counting a) (Counting b) = Counting (a * b)
  conquer = Counting 1

instance Decidable Counting where
  lose _ = Counting 0
  choose _ (Counting a) (Counting b) = Counting (a + b)


