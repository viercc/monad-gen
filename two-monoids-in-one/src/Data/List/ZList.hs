{-# LANGUAGE DeriveTraversable #-}

module Data.List.ZList where

import Control.Monad (ap)
import Data.List (genericReplicate)
import Data.Semigroup (stimes)

-- | List but ends in two ways.
--
-- If a list @(x :: ZList e a)@ ends with @Nil@,
-- concatenation @x <> y@ appends @y@ like usual list.
--
-- @
-- Cons a (Cons a' (... Nil)) <> y === Cons a (Cons a' (... y))
-- @
--
-- On the other hand, if @x@ ends with @Zee@,
-- concatenation from right @x <> y@ does not change @x@.
--
-- @
-- Cons a (Cons a' (... Zee)) <> _ === Cons a (Cons a' (... Zee))
-- @
data ZList e a = Nil | Zee e | Cons a (ZList e a)
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

instance Semigroup (ZList e a) where
  Nil <> y = y
  Zee e <> _ = Zee e
  Cons a x <> y = Cons a (x <> y)

  stimes b xs = foldr (<>) Nil (genericReplicate b xs)
  -- NB: @foldr@ is better here than the default implementation
  -- which performs "squaring" algorithm.

instance Monoid (ZList e a) where
  mempty = Nil

instance Applicative (ZList e) where
  pure a = Cons a Nil
  (<*>) = ap

instance Monad (ZList e) where
  Nil >>= _ = Nil
  Zee e >>= _ = Zee e
  Cons a x >>= k = k a <> (x >>= k)

fromList :: [a] -> ZList e a
fromList = foldr Cons Nil

mapMaybe :: (a -> Maybe b) -> ZList e a -> ZList e b
mapMaybe f = go
  where
    go Nil = Nil
    go (Zee e) = Zee e
    go (Cons a x) = case f a of
      Nothing -> go x
      Just b -> Cons b (go x)

-- | @ZList _ a@ is a monad too.
trap :: ZList e a -> (e -> ZList e' a) -> ZList e' a
trap Nil _ = Nil
trap (Zee e) k = k e
trap (Cons a x) y = Cons a (trap x y)