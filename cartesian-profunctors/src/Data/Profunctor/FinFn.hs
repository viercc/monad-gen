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
import GHC.TypeNats

import Data.Finite (Finite())
import qualified Data.Finite.Internal.Integral as Internal

-- | Function @a -> b@ with finite range.
data FinFn a b = FinFn !Integer (a -> Integer) (Integer -> b)

-- | Safe construction.
makeFinFn :: forall n a b.
             KnownNat n
          => (a -> Finite n) -> (Finite n -> b) -> FinFn a b
makeFinFn l r = FinFn (toInteger nvalue) (coerce l) (coerce r)
  where nvalue = natVal @n Proxy

-- | Safe pattern matching
withFinFn :: FinFn a b
          -> (forall n. KnownNat n => (a -> Finite n) -> (Finite n -> b) -> r)
          -> r
withFinFn (FinFn n l r) user =
    case someNatVal (fromInteger n) of
      SomeNat name -> user (upcast name . l) (r . downcast name)
  where
    upcast :: Proxy n -> Integer -> Finite n
    upcast _ = coerce
    downcast :: Proxy n -> Finite n -> Integer
    downcast _ = coerce

-- | @FinFn a b@ can be considered as a subtype of @a -> b@.
--
-- > applyFinFn fn >>> applyFinFn fn' === applyFinFn (fn >>>> fn')
applyFinFn :: FinFn a b -> a -> b
applyFinFn (FinFn _ l r) = l >>> r

-- | 'FinFn' is a semigroupoid. In other words, it composes like 'Control.Category.Category',
--   but it does not have 'Control.Category.id'.
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
fromMap m = FinFn (toInteger n) (toInteger . l) (r . fromInteger)
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

