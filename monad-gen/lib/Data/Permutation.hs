{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Data.Permutation(
  Permutation(..),
  applyPermutation,
  fromList,
  idPermutation,
  multPermutation,
  invPermutation,

  -- * Generating permutations
  permutationsN,
  fixingPermutations,
  fixingPermutationsSorted,

  Transposition(..),
  tr,
  fixingGeneratorsSorted
) where

import qualified Data.Foldable as F
import qualified Data.Vector.Unboxed as UV
import Data.Function (on)
import qualified Data.List as List
import qualified Data.Vector.Unboxed.Mutable as UVM
import Data.Maybe (fromMaybe)
import Prelude hiding (pi)

-- | Permutations.
-- 
-- >>> Just p1 = fromList [1,2,0] -- cyclic shift
-- >>> Just p2 = fromList [0,2,1] -- swap (1,2)
--
-- @idPermutation@ is identity
--
-- >>> p1 <> idPermutation == p1
-- True
-- >>> idPermutation <> p2 == p2
-- True
--
-- applyPermutation (p1 <> p2) === (applyPermutation p1 . applyPermutation p2)
-- 
-- >>> applyPermutation (p1 <> p2) <$> [0 .. 4]
-- [1,0,2,3,4]
-- >>> applyPermutation p1 . applyPermutation p2 <$> [0 .. 4]
-- [1,0,2,3,4]
--
-- inverse
--
-- >>> invPermutation p1
-- [2,0,1]
-- >>> invPermutation p1 <> p1
-- [0,1,2]
newtype Permutation = MkPermutation (UV.Vector Int)
   deriving (Eq, Ord)
   deriving newtype (Show)

instance Semigroup Permutation where
  (<>) = multPermutation

instance Monoid Permutation where
  mempty = idPermutation

applyPermutation :: Permutation -> Int -> Int
applyPermutation (MkPermutation p) i = fromMaybe i (p UV.!? i)

fromList :: [Int] -> Maybe Permutation
fromList xs
  | n == 0 = Just idPermutation
  | n == 1 = if xs == [0] then Just (MkPermutation (UV.fromList [0])) else Nothing
  | otherwise = fmap MkPermutation $ UV.createT $ do
      p <- UVM.replicate n n
      loop p 0 xs
  where
    n = length xs
    withinBound x = 0 <= x && x < n

    loop p _i [] = pure (Just p) -- successfully created the permutation
    loop p i (x : rest)
      | withinBound x = do
          -- p[i] += x
          -- (this does not affect whether p[i] < n or not since 0 <= x < n)
          UVM.modify p (x +) i
          -- If p[x] < n, it means we already subtracted the offset n,
          -- meaning there was a duplicate.
          px <- UVM.read p x
          if px < n
            then pure Nothing -- have duplicate: not a permutation
            else do UVM.write p x (px - n)
                    loop p (i + 1) rest
      | otherwise = pure Nothing

permutationsN :: Int -> [Permutation]
permutationsN n = MkPermutation <$> [ UV.fromList ys | ys <- List.permutations xs ]
  where
    xs = [0 .. n - 1]

idPermutation :: Permutation
idPermutation = MkPermutation UV.empty

multPermutation :: Permutation -> Permutation -> Permutation
multPermutation (MkPermutation p1) (MkPermutation p2) =
  case compare n1 n2 of
    EQ -> MkPermutation $ UV.backpermute p1 p2
    LT -> MkPermutation $ UV.backpermute (p1 <> UV.generate (n2 - n1) (n1 +)) p2
    GT -> MkPermutation $ UV.backpermute p1 (p2 <> UV.generate (n1 - n2) (n2 +))
  where
    n1 = UV.length p1
    n2 = UV.length p2

invPermutation :: Permutation -> Permutation
invPermutation (MkPermutation p) = MkPermutation $ UV.create $
  do q <- UVM.unsafeNew (UV.length p)
     F.for_ (zip [0..] (UV.toList p)) $ \(k, pk) ->
      UVM.write q pk k
     pure q

-- | @fixingPermutations@ but assumes the input is already sorted
fixingPermutationsSorted :: (Foldable f, Eq a) => f a -> [Permutation]
fixingPermutationsSorted fa = fmap F.fold . traverse (subPermutations n) $ permGroupsSorted fa
  where
    n = F.length fa

-- | Permutations on indices of list(ish) value @f a@,
--   which doesn't change its contents.
--
-- >>> -- permutes within indixes of same characters
-- >>> fixingPermutations "banana"
-- [[0,1,2,3,4,5],[0,1,4,3,2,5],[0,3,2,1,4,5],[0,3,4,1,2,5],[0,5,2,3,4,1],[0,5,4,3,2,1],[0,3,2,5,4,1],[0,3,4,5,2,1],[0,5,2,1,4,3],[0,5,4,1,2,3],[0,1,2,5,4,3],[0,1,4,5,2,3]]
--
-- >>> str = "banana"
-- >>> n = length str
-- >>> shuffle p = (\i -> str !! applyPermutation p i) <$> [0 .. n - 1]
-- >>> all (== str) $ shuffle <$> fixingPermutations str
-- True
fixingPermutations :: (Foldable f, Ord a) => f a -> [Permutation]
fixingPermutations fa = fmap F.fold . traverse (subPermutations n) $ permGroups fa
  where
    n = length fa

permGroupsSorted :: (Foldable f, Eq a) => f a -> [[Int]]
permGroupsSorted labels = groups
  where
    indices = zip [0..] (F.toList labels)
    groups = fmap fst <$> List.groupBy ((==) `on` snd) indices

permGroups :: (Foldable f, Ord a) => f a -> [[Int]]
permGroups labels = groups
  where
    indices = List.sortOn snd $ zip [0..] (F.toList labels)
    groups = fmap fst <$> List.groupBy ((==) `on` snd) indices

subPermutations :: Int -> [Int] -> [Permutation]
subPermutations n xs = MkPermutation <$> [ iota UV.// zip xs ys | ys <- List.permutations xs ]
  where
    iota = UV.generate n id

----

data Transposition = Transpose Int Int
  deriving (Show)

tr :: Transposition -> Int -> Int
tr (Transpose a b) = f
  where
    f i
      | i == a = b
      | i == b = a
      | otherwise = i

-- | Generators of @fixingPermutationsSorted@
fixingGeneratorsSorted :: (Foldable f, Eq a) => f a -> [Transposition]
fixingGeneratorsSorted sig =
  [Transpose i j | ((i, n), (j, m)) <- zip labels (drop 1 labels), n == m]
  where
    labels = zip [0..] (F.toList sig)
