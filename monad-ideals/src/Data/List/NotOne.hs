{-# LANGUAGE DeriveTraversable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.List.NotOne
-- Copyright   :  (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
module Data.List.NotOne where

import Data.Maybe (mapMaybe)
import Data.Foldable (toList)

import Data.Functor.Bind
import Data.Functor.Plus (Alt(..), Plus(..))
import Control.Monad.Isolated

import Data.List.TwoOrMore

-- | List sans singleton
data NotOne a = Zero | Multiple (TwoOrMore a)
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

notOne :: [a] -> Either a (NotOne a)
notOne [] = Right Zero
notOne [a] = Left a
notOne (a1 : a2 : as) = Right . Multiple $ TwoOrMore a1 a2 as

getMultiple :: NotOne a -> Maybe (TwoOrMore a)
getMultiple Zero = Nothing
getMultiple (Multiple as) = Just as

instance Semigroup (NotOne a) where
  Zero <> bs = bs
  Multiple (TwoOrMore a1 a2 as) <> bs = Multiple $ TwoOrMore a1 a2 (as ++ toList bs)

instance Monoid (NotOne a) where
  mempty = Zero

instance Apply NotOne where
  Zero <.> _ = Zero
  Multiple _ <.> Zero = Zero
  Multiple as <.> Multiple bs = Multiple (as <.> bs)

instance Alt NotOne where
  (<!>) = (<>)

instance Plus NotOne where
  zero = mempty

-- | @(>>-) = flip foldMap@
instance Bind NotOne where
  Zero >>- _ = Zero
  Multiple as >>- k = case mapMaybe (getMultiple . k) (toList as) of
    [] -> Zero
    [bs] -> Multiple bs
    bs1 : bs2 : bss -> Multiple $ join (TwoOrMore bs1 bs2 bss)

instance Isolated NotOne where
  impureBind as k = Unite . notOne $ toList as >>= toList . k