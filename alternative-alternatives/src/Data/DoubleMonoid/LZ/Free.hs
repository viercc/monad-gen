{-# LANGUAGE DeriveTraversable #-}
module Data.DoubleMonoid.LZ.Free(
  Free(..),
  SummandF(..), injectSummand,
  FactorF(..), injectFactor,
  PList(..),

  viewSum, viewProd, mprodZ,

  -- * reexport
  ZList(..)
) where

import Data.Foldable (toList)
import Control.Monad (ap, (<=<))

import Data.DoubleMonoid
import Data.List.TwoOrMore

import Data.List.ZList (ZList(..))
import qualified Data.List.ZList as ZL

-- | Free left zero double monoid
data Free a =
    Lit a
  | Zero
  | One
  | SumOf (TwoOrMore (SummandF a))
  | ProdOf (PList (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | Non-zero expressions which can't be written as a sum (x /+/ y) 
data SummandF a = SummandLit a | SummandOne | SummandProd (PList (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

injectSummand :: SummandF a -> Free a
injectSummand (SummandLit a) = Lit a
injectSummand SummandOne = One
injectSummand (SummandProd xs) = ProdOf xs

-- | Non-zero, Non-one expressions which can't be written as a product (x /*/ y)
data FactorF a = FactorLit a | FactorSum (TwoOrMore (SummandF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

injectFactor :: FactorF a -> Free a
injectFactor (FactorLit a) = Lit a
injectFactor (FactorSum xs) = SumOf xs

-- | @ZList@ but there's at least two element, counting Zend as one element
data PList a = Pxz a | PLong a a (ZList a)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

pToZList :: PList a -> ZList a
pToZList (Pxz a) = Cons a Zend
pToZList (PLong a0 a1 as) = Cons a0 (Cons a1 as)

instance Semigroup (PList a) where
  Pxz a <> _ = Pxz a
  PLong a0 a1 as <> y = PLong a0 a1 (as <> pToZList y)

viewSum :: Free a -> [SummandF a]
viewSum (Lit a) = [SummandLit a]
viewSum Zero = []
viewSum One = [SummandOne]
viewSum (SumOf xs) = toList xs
viewSum (ProdOf xs) = [SummandProd xs]

viewProd :: Free a -> ZList (FactorF a)
viewProd (Lit a) = Cons (FactorLit a) Nend
viewProd Zero = Zend
viewProd One = Nend
viewProd (SumOf xs) = Cons (FactorSum xs) Nend
viewProd (ProdOf xs) = pToZList xs

mprodZ :: ZList (Free a) -> Free a
mprodZ xs = case xs >>= viewProd of
  Nend -> One
  Zend -> Zero
  Cons y Nend -> injectFactor y
  Cons y Zend -> ProdOf (Pxz y)
  Cons y0 (Cons y1 ys) -> ProdOf (PLong y0 y1 ys)

instance DoubleMonoid (Free a) where
  msum xs = case xs >>= viewSum of
    [] -> Zero
    [x] -> injectSummand x
    (x0:x1:rest) -> SumOf (TwoOrMore x0 x1 rest)
  
  mprod = mprodZ . ZL.fromList

instance Applicative Free where
  pure = Lit
  (<*>) = ap

instance Monad Free where
  Lit a >>= k = k a
  Zero >>= _ = Zero
  One >>= _ = One
  SumOf mas >>= k = msum $ fmap (k <=< injectSummand) (toList mas)
  ProdOf mas >>= k = mprodZ $ fmap (k <=< injectFactor) (pToZList mas)
