module Data.Array.Extra(
  module Data.Array,
  (!?),
  genArray,
  genArrayM,
  prettyArray
) where

import Data.Array

(!?) :: (Ix i) => Array i a -> i -> Maybe a
a !? i | inRange (bounds a) i = Just (a ! i)
       | otherwise = Nothing

infixl 9 !?

genArray :: (Ix i) => (i, i) -> (i -> a) -> Array i a
genArray r f = listArray r (f <$> range r)

genArrayM :: (Ix i, Monad f) => (i, i) -> (i -> f a) -> f (Array i a)
genArrayM r f = listArray r <$> mapM f (range r)

prettyArray :: (Ix i, Ix j, Show i, Show j, Show a) => Array (i,j) a -> [String]
prettyArray table = formatTable $ headerRow : map row xs
  where
    ((xLo, yLo), (xHi, yHi)) = bounds table
    xs = range (xLo, xHi)
    ys = range (yLo, yHi)
    headerRow = "" : map show ys
    row x = show x : [ show (table ! (x,y)) | y <- ys]

formatTable :: [[String]] -> [String]
formatTable cells = addHRule $ renderRow <$> cells
  where
    cellSizes = foldr (zipWith max) (repeat 0) [ length <$> row | row <- cells ]
    renderRow row = addVRule $ zipWith renderCell cellSizes row
    renderCell n cellStr = replicate (n - length cellStr) ' ' ++ cellStr ++ " "
    addVRule [] = []
    addVRule (headerCell : rest) = headerCell ++ "| " ++ concat rest
    addHRule [] = []
    addHRule (headerRow : rest) = headerRow : map hrule headerRow : rest
    hrule '|' = '+'
    hrule _ = '-'