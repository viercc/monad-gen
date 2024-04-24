{-# LANGUAGE DeriveTraversable #-}
module Data.List.TwoOrMore(TwoOrMore(..), twoOrMore, toNonEmpty) where

import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Semigroup.Foldable (Foldable1(..))

data TwoOrMore a = TwoOrMore a a [a]
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

instance Foldable1 TwoOrMore where
  foldMap1 f (TwoOrMore a1 a2 as) = f a1 <> foldMap1 f (a2 :| as)
  toNonEmpty (TwoOrMore a1 a2 as) = a1 :| (a2 : as)

twoOrMore :: NonEmpty a -> Either a (TwoOrMore a)
twoOrMore (a1 :| as) = case as of
  [] -> Left a1
  a2 : as' -> Right (TwoOrMore a1 a2 as')