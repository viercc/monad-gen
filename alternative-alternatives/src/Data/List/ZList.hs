{-# LANGUAGE DeriveTraversable #-}
module Data.List.ZList where

import Control.Monad (ap)

-- | List but ends in two ways.
--
-- If a list @(x :: ZList a)@ ends with @Nend@,
-- concatenation @x <> y@ appends @y@ like usual list.
--
-- @
-- Cons a (Cons a' (... Nend)) <> y === Cons a (Cons a' (... y))
-- @
-- 
-- On the other hand, if @x@ ends with @Zend@,
-- concatenation from right @x <> y@ does not change @x@.
--
-- @
-- Cons a (Cons a' (... Zend)) <> _ === Cons a (Cons a' (... Zend))
-- @
data ZList a = Nend | Zend | Cons a (ZList a)
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

instance Semigroup (ZList a) where
  Nend <> y = y
  Zend <> _ = Zend
  Cons a x <> y = Cons a (x <> y)

instance Monoid (ZList a) where
  mempty = Nend

instance Applicative ZList where
  pure a = Cons a Nend
  (<*>) = ap

instance Monad ZList where
  Nend >>= _ = Nend
  Zend >>= _ = Zend
  Cons a x >>= k = k a <> (x >>= k)

fromList :: [a] -> ZList a
fromList = foldr Cons Nend

mapMaybe :: (a -> Maybe b) -> ZList a -> ZList b
mapMaybe f = go
  where
    go Nend = Nend
    go Zend = Zend
    go (Cons a x) = case f a of
      Nothing -> go x
      Just b -> Cons b (go x)

-- | @trap@ does concatenation like '<>', but swaps the role of 'Nend' and 'Zend'.
trap :: ZList a -> ZList a -> ZList a
trap Nend _ = Nend
trap Zend y = y
trap (Cons a x) y = Cons a (trap x y)