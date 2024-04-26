{-# LANGUAGE DeriveTraversable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.List.TwoOrMore
-- Copyright   :  (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
module Data.List.TwoOrMore(TwoOrMore(..), twoOrMore, toNonEmpty) where

import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Semigroup.Foldable (Foldable1(..))

import Data.Functor.Bind
import Data.Functor.Alt (Alt(..))
import Control.Monad.Isolated
import Control.Monad.Ideal (MonadIdeal(..), impureBindDefault, Ideal, runIdeal)


-- | List of two or more elements
data TwoOrMore a = TwoOrMore a a [a]
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

instance Foldable1 TwoOrMore where
  foldMap1 f (TwoOrMore a1 a2 as) = f a1 <> foldMap1 f (a2 :| as)
  toNonEmpty (TwoOrMore a1 a2 as) = a1 :| (a2 : as)

twoOrMore :: NonEmpty a -> Either a (TwoOrMore a)
twoOrMore (a1 :| as) = case as of
  [] -> Left a1
  a2 : as' -> Right (TwoOrMore a1 a2 as')

instance Semigroup (TwoOrMore a) where
  TwoOrMore a1 a2 as <> bs = TwoOrMore a1 a2 (as ++ toList bs)

instance Apply TwoOrMore where
  TwoOrMore x1 x2 xs <.> TwoOrMore y1 y2 ys = TwoOrMore (x1 y1) (x1 y2) (fmap x1 ys ++ (x2 : xs <*> y1 : y2 : ys))

instance Alt TwoOrMore where
  (<!>) = (<>)

-- | @(>>-) = flip foldMap1@
instance Bind TwoOrMore where
  TwoOrMore a1 a2 as >>- k = case k a1 of
    TwoOrMore b1 b2 bs -> TwoOrMore b1 b2 $ bs ++ ((a2 : as) >>= toList . k)

instance Isolated TwoOrMore where
  impureBind = impureBindDefault

-- | @Ideal TwoOrMore ~ NonEmpty@
instance MonadIdeal TwoOrMore where
  idealBind as k = bindNonEmpty as (idealToNonEmpty . k)

idealToNonEmpty :: Ideal TwoOrMore a -> NonEmpty a
idealToNonEmpty = either pure toNonEmpty . runIdeal

bindNonEmpty :: TwoOrMore a -> (a -> NonEmpty b) -> TwoOrMore b
bindNonEmpty (TwoOrMore a1 a2 as) k = case (k a1, k a2) of
  (b1 :| [], b2 :| []) -> TwoOrMore b1 b2 $ as >>= toList . k
  (b1 :| [], b2 :| bs) -> TwoOrMore b1 b2 $ bs ++ (as >>= toList . k)
  (b1 :| b2 : bs, bs') -> TwoOrMore b1 b2 $ bs ++ toList bs' ++ (as >>= toList . k)