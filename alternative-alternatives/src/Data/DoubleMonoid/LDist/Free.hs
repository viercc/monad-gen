{-# LANGUAGE DeriveTraversable #-}
module Data.DoubleMonoid.LDist.Free where

import Control.Monad

-- | Free nearsemiring
newtype Free a = Free { getSummands :: [SummandF a] }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data SummandF a = One | Prod a (Free a)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Applicative Free where
  pure a = Free [ Prod a (Free [One]) ]
  (<*>) = ap

instance Monad Free where
  Free xs >>= k = Free $ xs >>= (getSummands . bindSummand k)

bindSummand :: (a -> Free b) -> SummandF a -> Free b
bindSummand _ One = Free [One]
bindSummand k (Prod a x) = k a `prod` (x >>= k)

prod :: Free a -> Free a -> Free a
prod (Free xs) y = Free $ xs >>= \x -> prodSummand x y

prodSummand :: SummandF a -> Free a -> [SummandF a]
prodSummand One y = getSummands y
prodSummand (Prod a x) y = [ Prod a (prod x y) ]