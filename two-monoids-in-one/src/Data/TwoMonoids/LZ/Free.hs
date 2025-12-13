{-# LANGUAGE DeriveTraversable #-}

module Data.TwoMonoids.LZ.Free
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
import Data.Foldable (toList)
import Data.List.TwoOrMore
import Data.List.ZList (ZList (..))
import qualified Data.List.ZList as ZL
import Data.List.ZList.Long (ZList' (..))
import qualified Data.List.ZList.Long as ZL'
import Data.Semigroup (Semigroup (..))
import Data.TwoMonoids.Class
import Data.TwoMonoids.LZ.Class

{-

Note: Category theory perspective

Free can be thought of the pushout (amalgamated product) of

\* List = [] = the free monoid monad
\* ZList = the free (monoid + right zero) monad

along

p1 :: Maybe ~> List
p1 Nothing = []
p1 (Just a) = pure a

p2 :: Maybe ~> ZList
p2 Nothing = Zee
p2 (Just a) = pure a

           p1
 Maybe ----------> List
   |                |
   |                |
   | p2             |
   |            +-- |
   v            |   v
 ZList ----------> Free

-}

-- | The free 'DMLZ'
data Free a
  = Lit a
  | Zero
  | One
  | SumOf (TwoOrMore (SummandF a))
  | ProdOf (ZList' () (FactorF a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | Non-zero expressions which can't be written as a sum (x /+/ y)
data SummandF a = SummandLit a | SummandOne | SummandProd (ZList' () (FactorF a))
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

viewProd :: Free a -> ZList () (FactorF a)
viewProd (Lit a) = Cons (FactorLit a) Nil
viewProd Zero = Zee ()
viewProd One = Nil
viewProd (SumOf xs) = Cons (FactorSum xs) Nil
viewProd (ProdOf xs) = ZL'.toZList xs

instance Semigroup (Free a) where
  sconcat = mprodZ . ZL.fromList . toList

instance Monoid (Free a) where
  mempty = One

instance TwoMonoids (Free a) where
  msum xs = case xs >>= viewSum of
    [] -> Zero
    [x] -> injectSummand x
    (x0 : x1 : rest) -> SumOf (TwoOrMore x0 x1 rest)

instance DMLZ (Free a) where
  mprodZ xs = case xs >>= viewProd of
    Nil -> One
    Zee _ -> Zero
    Cons y Nil -> injectFactor y
    Cons y (Zee _) -> ProdOf (Zxz y ())
    Cons y0 (Cons y1 ys) -> ProdOf (ZLong y0 y1 ys)

instance Applicative Free where
  pure = Lit
  (<*>) = ap

instance Monad Free where
  x >>= k = interpret k x

interpret :: (DMLZ b) => (a -> b) -> Free a -> b
interpret f = go
  where
    go (Lit a) = f a
    go Zero = zero
    go One = one
    go (SumOf xs) = msum $ toList (go . injectSummand <$> xs)
    go (ProdOf xs) = mprodZ $ ZL'.toZList (go . injectFactor <$> xs)