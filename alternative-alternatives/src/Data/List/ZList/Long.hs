{-# LANGUAGE DeriveTraversable #-}
module Data.List.ZList.Long where

import Data.List.ZList

-- | @ZList@ sans @'Nend', 'Zend', 'Cons' a 'Nend'@ 
data ZList' a = Zxz a | ZLong a a (ZList a)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

toZList :: ZList' a -> ZList a
toZList (Zxz a) = Cons a Zend
toZList (ZLong a0 a1 as) = Cons a0 (Cons a1 as)

instance Semigroup (ZList' a) where
  Zxz a <> _ = Zxz a
  ZLong a0 a1 as <> y = ZLong a0 a1 (as <> toZList y)
