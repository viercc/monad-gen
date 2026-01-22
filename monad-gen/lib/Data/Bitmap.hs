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

-- | Like @IntSet@ from containers, @(<>) = union@.
instance Semigroup Bitmap where
  (<>) = union
  stimes = stimesIdempotent

-- | Like @IntSet@ from containers, @(<>) = union@.
instance Monoid Bitmap where
  mempty = empty

-- | Singleton set. Negative arguments are silently ignored.
--
-- >>> singleton 0
-- Bitmap 1
-- >>> singleton 1
-- Bitmap 2
-- >>> singleton 2
-- Bitmap 4
singleton :: Int -> Bitmap
singleton i
  | i < 0 = empty
  | otherwise = Bitmap (bit i)

-- >>> fromList [0,1,2,1,3,1,5]
-- Bitmap 47
-- >>> foldMap singleton [0,1,2,1,3,1,5]
-- Bitmap 47
fromList :: [Int] -> Bitmap
fromList = Bitmap . foldl' (.|.) 0 . map bit . filter (>= 0)

-- * Queries

null :: Bitmap -> Bool
null = (empty ==)

member :: Int -> Bitmap -> Bool
member i s = i >= 0 && testBit s i

isInfiniteSet :: Bitmap -> Bool
isInfiniteSet (Bitmap x) = x < 0

-- >>> [(x, y) | x <- [0 .. 20], Just y <- [getSingleton (Bitmap x)] ]
-- [(1,0),(2,1),(4,2),(8,3),(16,4)]
--
-- >>> getSingleton (Bitmap (2^235))
-- Just 235
getSingleton :: Bitmap -> Maybe Int
getSingleton (Bitmap x)
  -- x <= 0 means either infinite set or empty set
  | x <= 0 = Nothing
  -- finite inhabited set
  | otherwise = case countTrailingZerosI x of
      Just (i,0) -> Just i
      _ -> Nothing

-- >>> toList (fromList [3,1,4,2,6,10,3])
-- [1,2,3,4,6,10]
toList :: Bitmap -> [Int]
toList (Bitmap x) = concat $ unfoldr step (0,x)
  where
    step (!_, 0) = Nothing
    step (!offset, !n) = case splitInteger n of
      (n', n0) -> Just (bitSetPositions offset n0, (offset + 64, n'))

bitSetPositions :: Int -> Word64 -> [Int]
bitSetPositions offset w = [ offset + i | i <- [0 .. 63], testBit w i ]

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
