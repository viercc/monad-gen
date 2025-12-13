{-# LANGUAGE DeriveTraversable #-}

module Data.TwoMonoids.LZLC.Free
  ( Free (..),
    SummandF (..),
    injectSummand,
    FactorF (..),
    injectFactor,
    interpret,
    viewSum,
    viewProd,
    mprodZ,

    -- * reexport
    ZList (..),
    ZList' (..),
  )
where

import Control.Monad (ap)
import Data.Foldable (Foldable (toList))
import Data.List.ZList (ZList (..))
import qualified Data.List.ZList as ZL
import Data.List.ZList.Long (ZList' (..))
import qualified Data.List.ZList.Long as ZL'
import Data.Semigroup (Semigroup (..))
import Data.TwoMonoids.Class
import Data.TwoMonoids.LZ.Class
import Data.TwoMonoids.LZLC.Class

{-

Note: Category theory perspective

Free can be thought of the pushout (amalgamated product) of
two copies of ZList.

\* Sum = ZList = the free (monoid + right zero) monad
\* Prod = ZList

from

type Short a = Either Constant a
data Constant = Zero | One

p1 :: Short ~> Sum
p1 (Left Zero) = Nil
p1 (Left One) = (Zee ())
p1 (Right a) = pure a

p2 :: Short ~> Prod
p2 (Left Zero) = (Zee ())
p2 (Left One) = Nil
p2 (Right a) = pure a

           p1
 Short ----------> Sum
   |                |
   |                |
   | p2             |
   |            +-- |
   v            |   v
  Prod ----------> Free

-}

-- | The free 'DMLZLC'.
data Free a
  = Lit a
  | Zero
  | One
  | SumOf (ZList' () (SummandF a))
  | ProdOf (ZList' () (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data SummandF a
  = SummandLit a
  | SummandProd (ZList' () (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

injectSummand :: SummandF a -> Free a
injectSummand (SummandLit a) = Lit a
injectSummand (SummandProd xs) = ProdOf xs

data FactorF a
  = FactorLit a
  | FactorSum (ZList' () (SummandF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

injectFactor :: FactorF a -> Free a
injectFactor (FactorLit a) = Lit a
injectFactor (FactorSum xs) = SumOf xs

viewSum :: Free a -> ZList () (SummandF a)
viewSum (Lit a) = pure (SummandLit a)
viewSum Zero = Nil
viewSum One = Zee ()
viewSum (SumOf xs) = ZL'.toZList xs
viewSum (ProdOf xs) = pure (SummandProd xs)

viewProd :: Free a -> ZList () (FactorF a)
viewProd (Lit a) = pure (FactorLit a)
viewProd Zero = Zee ()
viewProd One = Nil
viewProd (SumOf xs) = pure (FactorSum xs)
viewProd (ProdOf xs) = ZL'.toZList xs

instance Semigroup (Free a) where
  sconcat = mprodZ . ZL.fromList . toList

instance Monoid (Free a) where
  mempty = One

instance TwoMonoids (Free a) where
  msum = msumZ . ZL.fromList

instance DMLZ (Free a) where
  mprodZ xs = case xs >>= viewProd of
    Nil -> One
    Zee () -> Zero
    Cons y Nil -> injectFactor y
    Cons y (Zee ()) -> ProdOf (Zxz y ())
    Cons y0 (Cons y1 ys) -> ProdOf (ZLong y0 y1 ys)

instance DMLZLC (Free a) where
  msumZ xs = case xs >>= viewSum of
    Nil -> One
    Zee () -> Zero
    Cons y Nil -> injectSummand y
    Cons y (Zee ()) -> SumOf (Zxz y ())
    Cons y0 (Cons y1 ys) -> SumOf (ZLong y0 y1 ys)

instance Applicative Free where
  pure = Lit
  (<*>) = ap

instance Monad Free where
  x >>= k = interpret k x

interpret :: (DMLZLC b) => (a -> b) -> Free a -> b
interpret f = go
  where
    go (Lit a) = f a
    go Zero = zero
    go One = one
    go (SumOf xs) = msumZ $ ZL'.toZList (go . injectSummand <$> xs)
    go (ProdOf xs) = mprodZ $ ZL'.toZList (go . injectFactor <$> xs)