{-# LANGUAGE DeriveTraversable #-}
module Data.List.NotOne where

import Data.List.TwoOrMore

data NotOne a = Zero | Multiple (TwoOrMore a)
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

notOne :: [a] -> Either a (NotOne a)
notOne [] = Right Zero
notOne [a] = Left a
notOne (a1 : a2 : as) = Right . Multiple $ TwoOrMore a1 a2 as