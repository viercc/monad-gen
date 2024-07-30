{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Always import this module qualified!
module Data.DoubleMonoid.Free(
  Free(
    Free,
    runFree,
    Lit, Zero, One, (:/+/), (:/*/),
    Sum, Prod
  ),
  lit, sum, viewSum, prod, viewProd
) where

import Prelude hiding (sum)
import Data.Foldable (toList)
import Data.Bifunctor (Bifunctor(..))
import Control.Monad (join)

import qualified Data.List.NotOne as NotOne
import Data.List.NotOne (NotOne(), notOne)

import Control.Monad.Isolated
import Control.Monad.Coproduct
import Data.Functor.Classes (Show1 (..), showsUnaryWith, showsPrec1)
import Text.Show (showListWith)

newtype Free a = Free
  { runFree :: Unite (NotOne :+ NotOne) a}
  deriving stock (Eq, Functor, Foldable, Traversable)
  deriving newtype (Applicative, Monad)

unwrapMutual1 :: Foldable f => Mutual Either f g a -> [Unite (f :+ g) a]
unwrapMutual1 = map (Unite . second (Coproduct . Right)) . toList . runMutual

unwrapMutual2 :: Foldable g => Mutual Either g f a -> [Unite (f :+ g) a]
unwrapMutual2 = map (Unite . second (Coproduct . Left)) . toList . runMutual

instance Show a => Show (Free a) where
  showsPrec = showsPrec1

instance Show1 Free where
  liftShowsPrec showsA _ = go
    where
      go p (Lit a) = showsUnaryWith showsA "Lit" p a
      go p (Sum xs) = case xs of
        [] -> ("Zero" ++)
        [Prod xs'] -> case xs' of
          [] -> ("One" ++)
          _ -> showsUnaryWith goList "Prod" p xs'
        _ -> showsUnaryWith goList "Sum" p xs
      
      goList _ = showListWith (go 0)

pattern Lit :: a -> Free a
pattern Lit a = Free (Unite (Left a))

pattern Zero :: Free a
pattern Zero = Free (Unite (Right (Coproduct (Right (Mutual NotOne.Zero)))))

pattern One :: Free a
pattern One = Free (Unite (Right (Coproduct (Left (Mutual NotOne.Zero)))))

pattern (:/+/) :: Free a -> Free a -> Free a
pattern x :/+/ y <- (viewSum2 -> Just (x,y)) where
  x :/+/ y = sum [x,y]

viewSum2 :: Free a -> Maybe (Free a, Free a)
viewSum2 x = case viewSum x of
  (x0 : x1 : rest) -> Just (x0, sum (x1 : rest))
  _ -> Nothing

pattern Prod :: [Free a] -> Free a
pattern Prod xs <- (viewProd -> xs) where
  Prod xs = prod xs

pattern (:/*/) :: Free a -> Free a -> Free a
pattern x :/*/ y <- (viewProd2 -> Just (x,y)) where
  x :/*/ y = prod [x,y]

viewProd2 :: Free a -> Maybe (Free a, Free a)
viewProd2 x = case viewProd x of
  (x0 : x1 : rest) -> Just (x0, prod (x1 : rest))
  _ -> Nothing

pattern Sum :: [Free a] -> Free a
pattern Sum xs <- (viewSum -> xs) where
  Sum xs = sum xs

{-# COMPLETE Prod #-}
{-# COMPLETE Sum #-}
{-# COMPLETE Lit, Zero, One, (:/+/), (:/*/) #-}

-- | Literal
lit :: a -> Free a
lit = Lit

-- | Product operation on free double monoid
prod :: [Free a] -> Free a
prod xs = case notOne xs of
  Left x -> x
  Right xs' -> join $ Free (Unite . Right $ inject1 xs')

-- | Sum operation on free double monoid
sum :: [Free a] -> Free a
sum xs = case notOne xs of
  Left x -> x
  Right xs' -> join $ Free (Unite . Right $ inject2 xs')

-- | Decompose @x@ to products.
viewProd :: Free a -> [Free a]
viewProd x = case runUnite (runFree x) of
  Left a -> [pure a]
  Right (Coproduct (Left xs)) -> Free <$> unwrapMutual1 xs
  Right (Coproduct (Right _)) -> [x]

-- | Decompose @x@ to sums.
viewSum :: Free a -> [Free a]
viewSum x = case runUnite (runFree x) of
  Left a -> [pure a]
  Right (Coproduct (Left _))   -> [x] 
  Right (Coproduct (Right xs)) -> Free <$> unwrapMutual2 xs

