module Data.IntervalSet (
  IntervalSet(),
  toIntervals, toList,
  fromIntervals, fromList,

  empty, insert
) where

import qualified Data.IntMap.Strict as IntMap

-- | @IntSet@ but managed as set of \"runs\".
--   Runs are contiguous subsets of Int which
--   does not intersect or adjacent each other.
--
--   Each run are represented as lower-inclusive and upper-exclusive
--   intervals `[lo,hi)`. The set of runs is represented as a IntMap
--   which maps lower bound to upper bound.
--   
--   Invariant:
--     toIntervals is' = [ (a0,b0), (a1,b1), ... ]
--       => a0 < b0 < a1 < b1 < ...
newtype IntervalSet = IS (IntMap.IntMap Int)
  deriving (Show, Eq, Ord)

toIntervals :: IntervalSet -> [(Int,Int)]
toIntervals (IS m) = IntMap.toAscList m 

toList :: IntervalSet -> [Int]
toList = concatMap (\(lo,hi) -> [lo .. hi - 1]) . toIntervals

fromIntervals :: [(Int,Int)] -> IntervalSet
fromIntervals = foldl' (flip insert) empty

-- |
--
-- >>> fromList [3,4,5, 8,9]
-- IS (fromList [(3,6),(8,10)])
fromList :: [Int] -> IntervalSet
fromList = fromIntervals . map (\i -> (i, i+1))

empty :: IntervalSet
empty = IS IntMap.empty

-- | @cutAt k s@ Cuts IntervalSet at "lower half" (i < k) and "higher half" (k <= i).
cutAt :: Int -> IntervalSet -> (IntervalSet, IntervalSet)
cutAt k (IS m) = case IntMap.splitLookup k m of
  (lesser, Just hiK, greater) ->
    let greater' = IntMap.insert k hiK greater
    in (IS lesser, IS greater')
  (lesser, Nothing, greater) -> case IntMap.maxViewWithKey lesser of
    Nothing  -> (IS IntMap.empty, IS greater)
    Just ((loLast, hiLast), lesser') ->
      let lesser''  = IntMap.insert loLast (min k hiLast) lesser'
          greater'' | k < hiLast = IntMap.insert k hiLast greater
                    | otherwise  = greater
      in (IS lesser'', IS greater'') 

{-

>>> s0 = empty
>>> s1 = insert (3,6) s0  --- [3,4,5]
>>> s1
IS (fromList [(3,6)])

>>> s2 = insert (8,10) s1  --- [3,4,5,8,9]
>>> s2
IS (fromList [(3,6),(8,10)])

>>> insert (5,7) s2
IS (fromList [(3,7),(8,10)])
>>> insert (5,8) s2
IS (fromList [(3,10)])
-}
insert :: (Int, Int) -> IntervalSet -> IntervalSet
insert (lo,hi) s
  | lo >= hi = s
  | otherwise = IS m'
  where
    (IS lesser, _) = cutAt lo s
    (_, IS greater) = cutAt hi s
    (newLesser, newLo) = case IntMap.maxViewWithKey lesser of
      Nothing -> (IntMap.empty, lo)
      Just ((lastLo, lastHi), lesser')
        | lo <= lastHi -> (lesser', lastLo)    -- connected case
        | otherwise    -> (lesser, lo)         -- disconnected case
    (newGreater, newHi) = case IntMap.minViewWithKey greater of
      Nothing -> (IntMap.empty, hi)
      Just ((firstLo, firstHi), greater')
        | firstLo <= hi -> (greater', firstHi) -- connected case
        | otherwise     -> (greater, hi)       -- diconnected case
    
    m' = IntMap.insert newLo newHi $ IntMap.union newLesser newGreater
