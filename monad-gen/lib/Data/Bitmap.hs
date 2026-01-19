{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
-- | Use 'Integer' as set of non-negative integers.
--
-- (negative integers are silently ignored throughout this module)
module Data.Bitmap(
  Bitmap(..),
  fromList, toList,

  -- * Construction
  empty, full, union, intersection,
  singleton,

  -- * Query
  null, member, isInfiniteSet, getSingleton,
) where

import Prelude hiding (null)
import Data.Bits
import Data.Semigroup (Semigroup(..), stimesIdempotent)
import Data.Word (Word64)
import Data.List (unfoldr)

-- | Set of non-negative integers.
newtype Bitmap = Bitmap Integer
  deriving (Show, Read, Eq, Ord, Bits)

empty :: Bitmap
empty = Bitmap 0

full :: Bitmap
full = Bitmap (-1)

union :: Bitmap -> Bitmap -> Bitmap
union = (.|.)

intersection :: Bitmap -> Bitmap -> Bitmap
intersection = (.&.)

-- | Unlike @IntSet@ from containers, @(<>) = intersection@.
instance Semigroup Bitmap where
  (<>) = intersection
  stimes = stimesIdempotent

-- | Unlike @IntSet@ from containers, @(<>) = intersection@.
instance Monoid Bitmap where
  mempty = full

-- | Singleton set. Negative arguments are silently ignored.
singleton :: Int -> Bitmap
singleton i
  | i < 0 = empty
  | otherwise = Bitmap (bit i)

fromList :: [Int] -> Bitmap
fromList = Bitmap . foldl' (.|.) 0 . map bit . filter (>= 0)

-- * Queries

null :: Bitmap -> Bool
null = (empty ==)

member :: Int -> Bitmap -> Bool
member i s = i >= 0 && testBit s i

isInfiniteSet :: Bitmap -> Bool
isInfiniteSet (Bitmap x) = x < 0

getSingleton :: Bitmap -> Maybe Int
getSingleton (Bitmap x)
  -- x <= 0 means either infinite set or empty set
  | x <= 0 = Nothing
  -- finite inhabited set
  | otherwise = case countTrailingZerosI x of
      Just (i,0) -> Just i
      _ -> Nothing

toList :: Bitmap -> [Int]
toList (Bitmap x) = unfoldr countTrailingZerosI x

splitInteger :: Integer -> (Integer, Word64)
splitInteger x = (x `shiftR` 64, fromIntegral x)

-- |
-- 
-- >>> countTrailingZerosI 3
-- Just (0,1)
--
-- >>> countTrailingZerosI 0x100100
-- Just (8,2048)
--
-- >>> countTrailingZerosI (2 ^ (135 :: Int))
-- Just (135,0)
--
-- >>> countTrailingZerosI (-1)
-- Just (0,-1)
--
-- >>> countTrailingZerosI 0
-- Nothing
countTrailingZerosI :: Integer -> Maybe (Int, Integer)
countTrailingZerosI n
  | n == 0 = Nothing
  | otherwise = Just $ loop 0 n
  where
    loop !acc x = case splitInteger x of
      (x', 0) -> loop (acc + 64) x'
      (x', low) ->
        let k = countTrailingZeros low
        in (acc + k, (x' `shiftL` 64 .|. fromIntegral low) `shiftR` (k + 1))
