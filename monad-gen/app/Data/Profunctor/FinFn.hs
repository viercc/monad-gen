{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Profunctor.FinFn(
  FinFn(),
  makeFinFn,
  withFinFn,
  applyFinFn,
  (>>>>),
  (<<<<),

  fromMap,
) where

import Data.Coerce

import Control.Category ((>>>))
import Data.Profunctor
import Data.Profunctor.Cartesian

import qualified Data.Map as Map

import Data.Proxy
import Data.Reflection
import Data.IntRange.Unsafe

data FinFn a b = FinFn !Int (a -> Int) (Int -> b)

-- | Safe construction
makeFinFn :: forall n a b.
             Reifies n Int
          => (a -> UpTo n) -> (UpTo n -> b) -> FinFn a b
makeFinFn l r = FinFn nvalue (coerce l) (coerce r)
  where nvalue = reflect @n Proxy

-- | Safe pattern matching
withFinFn :: FinFn a b
          -> (forall n. Reifies n Int => (a -> UpTo n) -> (UpTo n -> b) -> r)
          -> r
withFinFn (FinFn n l r) user =
    reify n (\name -> user (upcast name . l) (r . downcast name))
  where
    upcast :: Proxy n -> Int -> UpTo n
    upcast _ = coerce
    downcast :: Proxy n -> UpTo n -> Int
    downcast _ = coerce

-- | How I would say... 'applyFinFn' is nice, functor-ish.
--   It commutes with 'Profunctor', 'Cartesian', 'Cocartesian',
--   and composition '(>>>>)'.
applyFinFn :: FinFn a b -> a -> b
applyFinFn (FinFn _ l r) = l >>> r

-- | 'FinFn' composes like 'Control.Category.Category', but can't be a Category since
--   it does not have 'Control.Cateogory.id'.
(>>>>) :: FinFn a b -> FinFn b c -> FinFn a c
(>>>>) (FinFn n l r) (FinFn m s t)
  | n <= m    = FinFn n l (r >>> s >>> t)
  | otherwise = FinFn m (l >>> r >>> s) t

infixr 1 >>>>

-- | > (<<<<) = flip (>>>>)
(<<<<) :: FinFn b c -> FinFn a b -> FinFn a c
(<<<<) = flip (>>>>)

infixr 1 <<<<

-- * Special constructions

-- | > applyFinFn . fromMap = flip Map.lookup
fromMap :: (Ord a) => Map.Map a b -> FinFn a (Maybe b)
fromMap m = FinFn n l r
  where
    n = 1 + Map.size m
    l a = maybe 0 (1+) $ Map.lookupIndex a m
    r 0 = Nothing
    r i = Just . snd $ Map.elemAt (i-1) m

instance Profunctor FinFn where
  dimap l r (FinFn n l' r') = FinFn n (l >>> l') (r' >>> r)

instance Cartesian FinFn where
  proUnit = FinFn 1 (const 0) (const ())
  FinFn n l r *** FinFn m s t = FinFn (n*m) ls rt
    where
      ls (a,a') = l a * m + s a'
      rt i = let (j,k) = i `quotRem` m
             in (r j, t k)

instance Cocartesian FinFn where
  proEmpty = FinFn 0 (error "empty function") (error "empty function")
  FinFn n l r +++ FinFn m s t = FinFn (n+m) ls rt
    where
      ls = either l ((n +) . s)
      rt i | i < n     = Left (r i)
           | otherwise = Right (t (i-n))

