{-# LANGUAGE DeriveFunctor #-}
module Data.DoubleMonoid.NearSemiring.Free where

import Control.Monad (ap)

import Data.DoubleMonoid.Class
import Data.DoubleMonoid.LZ.Class
import Data.DoubleMonoid.NearSemiring.Class

-- | The free 'NearSemiring'
newtype Forest a = SumOf [Tree a]
   deriving (Show, Eq, Ord, Functor)

data Tree a = One | a :/*/ Forest a
   deriving (Show, Eq, Ord, Functor)

instance DoubleMonoid (Forest a) where
  zero = SumOf []
  one = SumOf [One]
  SumOf xs /+/ SumOf ys = SumOf (xs ++ ys)
  (/*/) = multFF
    where
      multFF :: Forest a -> Forest a -> Forest a
      multFF (SumOf xs) y = SumOf $ xs >>= (`multTF` y)

      multTF :: Tree a -> Forest a -> [Tree a]
      multTF One (SumOf ys) = ys
      multTF (a :/*/ x) y = [ a :/*/ multFF x y ]

instance DMLZ (Forest a)
instance NearSemiring (Forest a)

interpret :: NearSemiring b => (a -> b) -> Forest a -> b
interpret f = go
  where
    go (SumOf xs) = msum (go' <$> xs)
    go' One = one
    go' (a :/*/ x) = f a /*/ go x

instance Applicative Forest where
  pure a = SumOf [a :/*/ one]
  (<*>) = ap

instance Monad Forest where
  x >>= k = interpret k x
