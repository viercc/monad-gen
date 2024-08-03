{-# LANGUAGE DeriveTraversable #-}
module Data.DoubleMonoid.LZ.Free(
  Free(..),
  SummandF(..), injectSummand,
  FactorF(..), injectFactor,

  viewSum, viewProd, mprodZ,

  -- * reexport
  ZList(..), ZList'(..)
) where

import Data.Foldable (toList)
import Control.Monad (ap, (<=<))

import Data.List.TwoOrMore

import Data.List.ZList (ZList(..))
import Data.List.ZList.Long (ZList'(..))
import qualified Data.List.ZList as ZL
import qualified Data.List.ZList.Long as ZL'

import Data.DoubleMonoid.Class
import Data.DoubleMonoid.LZ.Class

-- | Free left zero double monoid
data Free a =
    Lit a
  | Zero
  | One
  | SumOf (TwoOrMore (SummandF a))
  | ProdOf (ZList' (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | Non-zero expressions which can't be written as a sum (x /+/ y) 
data SummandF a = SummandLit a | SummandOne | SummandProd (ZList' (FactorF a))
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
viewProd (ProdOf xs) = ZL'.toZList xs

instance DoubleMonoid (Free a) where
  msum xs = case xs >>= viewSum of
    [] -> Zero
    [x] -> injectSummand x
    (x0:x1:rest) -> SumOf (TwoOrMore x0 x1 rest)
  
  mprod = mprodZ . ZL.fromList

instance DMLZ (Free a) where
  mprodZ xs = case xs >>= viewProd of
    Nend -> One
    Zend -> Zero
    Cons y Nend -> injectFactor y
    Cons y Zend -> ProdOf (Zxz y)
    Cons y0 (Cons y1 ys) -> ProdOf (ZLong y0 y1 ys)

instance Applicative Free where
  pure = Lit
  (<*>) = ap

instance Monad Free where
  Lit a >>= k = k a
  Zero >>= _ = Zero
  One >>= _ = One
  SumOf mas >>= k = msum $ fmap (k <=< injectSummand) (toList mas)
  ProdOf mas >>= k = mprodZ $ fmap (k <=< injectFactor) (ZL'.toZList mas)
