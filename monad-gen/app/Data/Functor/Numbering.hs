{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase    #-}
module Data.Functor.Numbering(
  FromN(),
  withFromN,
  empty, singleton, generate,
  toList, fromList, vec,
  toVector, fromVector,
  
  imap, indexed, iota,
  
  zipWith, zipWith3, zip, zip3,
  alignWith,
  
  (!),

  filter, mapMaybe,

) where

import Prelude hiding (zipWith, zipWith3, zip, zip3, filter)
import qualified Prelude
import qualified Data.Maybe (mapMaybe)

import qualified Control.Applicative
import Control.Monad
import Control.Monad.Fix

import Data.Semigroup
import Data.Foldable
import qualified Data.Vector as V

import Data.Coerce

import Data.Reflection
import Data.IntRange.Unsafe

data FromN a = FromN !Int (Int -> a)
    deriving Functor

-- * Safe pattern matching
withFromN :: FromN a -> (forall n. Reifies n Int => (UpTo n -> a) -> r) -> r
withFromN (FromN n f) user = reify n (\name -> user (f . downcast name))
  where
    downcast :: proxy n -> UpTo n -> Int
    downcast _ = coerce

-- * Core construction
empty :: FromN a
empty = FromN 0 (\_ -> error "FromN.empty")

singleton :: a -> FromN a
singleton a = FromN 1 (const a)

generate :: Int -> (Int -> a) -> FromN a
generate n = FromN (max n 0)

-- * Accessing
(!) :: FromN a -> Int -> a
FromN n f ! i | 0 <= i && i < n = f i
            | otherwise       = error $ "out of bounds:" ++ show i ++ " for FromN with length " ++ show n

-- * Conversion
toVector :: FromN a -> V.Vector a
toVector (FromN n f) = V.generate n f

fromVector :: V.Vector a -> FromN a
fromVector v = FromN (V.length v) (V.unsafeIndex v)

fromList, vec :: [a] -> FromN a
vec = fromVector . V.fromList
fromList = vec

-- * Index
imap :: (Int -> a -> b) -> FromN a -> FromN b
imap u (FromN n f) = FromN n (\i -> u i (f i))

indexed :: FromN a -> FromN (Int, a)
indexed = imap (,)

iota :: Int -> FromN Int
iota n = FromN n id

-- * Zip/Align
zip :: FromN a -> FromN b -> FromN (a, b)
zip = zipWith (,)

zip3 :: FromN a -> FromN b -> FromN c -> FromN (a, b, c)
zip3 = zipWith3 (,,)

zipWith :: (a -> b -> c) -> FromN a -> FromN b -> FromN c
zipWith u (FromN n f) (FromN m g) = FromN (min n m) (\i -> u (f i) (g i))

zipWith3 :: (a -> b -> c -> d) -> FromN a -> FromN b -> FromN c -> FromN d
zipWith3 u as bs cs = zipWith ($) (zipWith u as bs) cs

alignWith :: (a -> r) -> (b -> r) -> (a -> b -> r) -> FromN a -> FromN b -> FromN r
alignWith this that these (FromN n f) (FromN m g) = FromN (max n m) h
  where h | n < m     = \i -> if i < n then these (f i) (g i) else that (g i)
          | n == m    = \i -> these (f i) (g i)
          | otherwise = \i -> if i < m then these (f i) (g i) else this (f i)

-- * Non-lazy operations: resulted FromN will be backed by concrete Vectors
filter :: (a -> Bool) -> FromN a -> FromN a
filter p = vec . Prelude.filter p . toList

mapMaybe :: (a -> Maybe b) -> FromN a -> FromN b
mapMaybe f = vec . Data.Maybe.mapMaybe f . toList

instance (Show a) => Show (FromN a) where
  show v = "vec " ++ show (toList v)

instance Foldable FromN where
  null (FromN n _) = n == 0
  length (FromN n _) = n
  foldMap g (FromN n f) = foldMap (g . f) [0..n-1]

instance Traversable FromN where
  traverse f (FromN n g) = fromVector <$> traverse (f . g) (V.generate n id)
  mapM f (FromN n g) = fromVector <$> mapM (f . g) (V.generate n id)

instance Applicative FromN where
  pure = singleton
  FromN m f <*> FromN n g = FromN (m * n) h
    where h i = f (i `div` n) (g (i `mod` n))
  FromN m _  *> FromN n g = FromN (m * n) h
    where h i = g (i `mod` n)
  FromN m f <*  FromN n _ = FromN (m * n) h
    where h i = f (i `div` n)

instance Control.Applicative.Alternative FromN where
  empty = empty
  (<|>) = (<>)

instance Monad FromN where
  return = pure
  ma >>= k | n <= 0   = empty
           | n <= 255 = foldMap k ma
           | otherwise = treeMerge (k <$> toList ma)
    where n = length ma
  (>>) = (*>)

instance MonadFail FromN where
  fail _ = empty

instance MonadPlus FromN where
  mzero = empty
  mplus = (<>)

instance MonadFix FromN where
  mfix f = FromN n h
    where bottom = error "Argument of mfix (f :: a -> m a) shouldn't force its argument!"
          n = length (f bottom)
          h i = fix (\a -> f a ! i)

instance (Eq a) => Eq (FromN a) where
  v1 == v2 = length v1 == length v2 && toList v1 == toList v2

instance (Ord a) => Ord (FromN a) where
  compare v1 v2 = compare (toList v1) (toList v2)

instance Semigroup (FromN a) where
  FromN 0 _ <> b       = b
  a       <> FromN 0 _ = a
  FromN m f <> FromN n g = FromN (m + n) h
    where h i = if i < m then f i else g (i - m)

  stimes n a | n >= 0    = FromN (fromIntegral n) id *> a
             | otherwise = error ("Negative exponent:" ++ show (toInteger n))
  sconcat = treeMerge . toList

instance Monoid (FromN a) where
  mempty = empty
  mconcat = treeMerge

treeMerge :: [FromN a] -> FromN a
treeMerge = foldl' (flip (<>))  empty . doublingSeq . Prelude.filter (not . null)
  where
    doublingSeq = foldl' step []
    step [] xs = [xs]
    step (ys:rest) xs
        | 2 * length xs <= length ys = xs : ys : rest
        | otherwise                  = step rest (ys <> xs)
