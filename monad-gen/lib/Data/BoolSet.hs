{-# LANGUAGE TypeApplications #-}
module Data.BoolSet(
  BoolSet(),
  singleton, toList, fromList,
  empty, full, uniqueBool,
  union, unions, intersection, intersections
) where
import Data.Bool (bool)
import Data.Bits
import Data.Coerce (coerce)

-- | @Set Bool@
newtype BoolSet = BoolSet Int
  deriving (Eq, Ord, Show)

-- | '<>' = 'union' but lazy in y
instance Semigroup BoolSet where
  x <> y
    | x == full = full
    | otherwise = union x y

instance Monoid BoolSet where
  mempty = BoolSet 0

singleton :: Bool -> BoolSet
singleton = BoolSet . bool 1 2

toList :: BoolSet -> [Bool]
toList (BoolSet a) = [False | testBit a 0] ++ [True | testBit a 1]

fromList :: [Bool] -> BoolSet
fromList = BoolSet . loop 0
  where
    loop 3 _ = 3
    loop a [] = a
    loop a (b:bs) = loop (a .|. bool 1 2 b) bs

empty :: BoolSet
empty = BoolSet 0

full :: BoolSet
full = BoolSet 3

uniqueBool :: BoolSet -> Maybe Bool
uniqueBool (BoolSet a) = case a of
  1 -> Just False
  2 -> Just True
  _ -> Nothing

union :: BoolSet -> BoolSet -> BoolSet
union = coerce ((.|.) @Int)

unions :: [BoolSet] -> BoolSet
unions = loop empty
  where
    loop x ys
      | x == full = full
      | otherwise = case ys of
          [] -> x
          y : rest -> loop (union x y) rest

intersection :: BoolSet -> BoolSet -> BoolSet
intersection = coerce ((.&.) @Int)

intersections :: [BoolSet] -> BoolSet
intersections = loop full
  where
    loop x ys
      | x == empty = empty
      | otherwise = case ys of
          [] -> x
          y : rest -> loop (intersection x y) rest
