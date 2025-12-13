{-# LANGUAGE DeriveTraversable #-}

module Data.List.ZList.Long where

import Data.List.ZList

-- | @ZList@ sans @'Nil', @'Zee' e@, 'Cons' a 'Nil'@
data ZList' e a = Zxz a e | ZLong a a (ZList e a)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

toZList :: ZList' e a -> ZList e a
toZList (Zxz a e) = Cons a (Zee e)
toZList (ZLong a0 a1 as) = Cons a0 (Cons a1 as)

instance Semigroup (ZList' e a) where
  Zxz a e <> _ = Zxz a e
  ZLong a0 a1 as <> y = ZLong a0 a1 (as <> toZList y)
