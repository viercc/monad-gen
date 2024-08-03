{-# LANGUAGE DeriveTraversable #-}
module Data.DoubleMonoid.LZLC.Free(
  Free(..),
  SummandF(..), injectSummand,
  FactorF(..), injectFactor,

  viewSum, viewProd, mprodZ,

  -- * reexport
  ZList(..), ZList'(..)
) where

import Control.Monad (ap, (<=<))

import Data.List.ZList (ZList(..))
import Data.List.ZList.Long (ZList'(..))
import qualified Data.List.ZList as ZL
import qualified Data.List.ZList.Long as ZL'

import Data.DoubleMonoid.Class
import Data.DoubleMonoid.LZ.Class
import Data.DoubleMonoid.LZLC.Class

data Free a =
    Lit a
  | Zero
  | One
  | SumOf (ZList' (SummandF a))
  | ProdOf (ZList' (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data SummandF a =
    SummandLit a
  | SummandProd (ZList' (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

injectSummand :: SummandF a -> Free a
injectSummand (SummandLit a) = Lit a
injectSummand (SummandProd xs) = ProdOf xs

data FactorF a =
    FactorLit a
  | FactorSum (ZList' (SummandF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

injectFactor :: FactorF a -> Free a
injectFactor (FactorLit a) = Lit a
injectFactor (FactorSum xs) = SumOf xs

viewSum :: Free a -> ZList (SummandF a)
viewSum (Lit a) = pure (SummandLit a)
viewSum Zero = Nend
viewSum One = Zend
viewSum (SumOf xs) = ZL'.toZList xs
viewSum (ProdOf xs) = pure (SummandProd xs)

viewProd :: Free a -> ZList (FactorF a)
viewProd (Lit a) = pure (FactorLit a)
viewProd Zero = Zend
viewProd One = Nend
viewProd (SumOf xs) = pure (FactorSum xs)
viewProd (ProdOf xs) = ZL'.toZList xs


instance DoubleMonoid (Free a) where
  msum = msumZ . ZL.fromList
  mprod = mprodZ . ZL.fromList

instance DMLZ (Free a) where
  mprodZ xs = case xs >>= viewProd of
    Nend -> One
    Zend -> Zero
    Cons y Nend -> injectFactor y
    Cons y Zend -> ProdOf (Zxz y)
    Cons y0 (Cons y1 ys) -> ProdOf (ZLong y0 y1 ys)

instance DMLZLC (Free a) where
  msumZ xs = case xs >>= viewSum of
    Nend -> One
    Zend -> Zero
    Cons y Nend -> injectSummand y
    Cons y Zend -> SumOf (Zxz y)
    Cons y0 (Cons y1 ys) -> SumOf (ZLong y0 y1 ys)

instance Applicative Free where
  pure = Lit
  (<*>) = ap

instance Monad Free where
  Lit a >>= k = k a
  Zero >>= _ = Zero
  One >>= _ = One
  SumOf mas >>= k = msumZ $ fmap (k <=< injectSummand) (ZL'.toZList mas)
  ProdOf mas >>= k = mprodZ $ fmap (k <=< injectFactor) (ZL'.toZList mas)
