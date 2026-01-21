{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}

module Data.PreNatMap(
  PreNatMap(),

  -- * initialize
  empty,
  
  -- * query
  isFull,
  fullMatch, match,
  lookup, lookupWith, lookupShape,

  -- * update
  refine, refineShape,

  -- * conversion
  toEntries, fromEntries, make,
  toNatMap, fromNatMap, toShapeMap, fromShapeMap,
) where

import Prelude hiding (lookup)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import Data.Foldable (Foldable(..))

import Data.FunctorShape
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector as V
import Control.Monad (guard)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Functor.Classes (showsUnaryWith)
import Data.NatMap (NatMap)
import qualified Data.NatMap as NM

import TraversableUtil (indices, zipMatch)
import qualified Data.Set as Set

-- | @PreNatMap f g@ represents a partially known
--   natural transformation @f ~> g@.
-- 
-- ==== Examples
-- 
-- @reverse@ is a natural transformation from list to list.
--
-- > reverse :: [a] -> [a]
-- 
-- Using 'refine' function, you can accumulate knowledge about how
-- @reverse@ behaves to @PreNatMap [] []@ through examples.
-- 
-- >>> p1 = refine "foo" "oof" empty
-- >>> p1
-- Just (make [([0,1,1],[1,1,0])])
--
-- You can add another example to strengthen the knowledge.
-- (The monadic bind @'>>='@ is used here because 'refine'
--  returns the result wrapped in @Maybe@.)
--
-- >>> p2 = p1 >>= refine "dad" "dad"
-- >>> p2
-- Just (make [([0,1,2],[2,1,0])])
--
-- >>> p3 = p2 >>= refine "aabb" "bbaa"
-- >>> p3
-- Just (make [([0,1,2],[2,1,0]),([0,0,1,1],[1,1,0,0])])
--
-- If you add an example contradicting to existing examples,
-- 'refine' can fail with @Nothing@.
-- 
-- >>> p3 >>= refine "cccd" "cddd"
-- Nothing
-- 
-- You can also query against the learned knowledge.
-- 'match' function takes an input and a 'PreNatMap', and
-- if the learned knowledge determine the output uniquely,
-- returns that output.
--
-- >>> p3 >>= match "ABC"
-- Just "CBA"
-- >>> p3 >>= match "XXYY"
-- Just "YYXX"
-- 
-- If the output is not unique, 'match' can fail,
-- even when the "shape" of the output is known.
-- In the following example, it is known that the output for a 4-lengthed list
-- is a 4-lengthed list again, but 'match' fails because the differences
-- in the list elements make the output ambiguous.
--
-- >>> p3 >>= match "XYZW"
-- Nothing
-- 
-- There is another query 'lookup' which always return
-- something for "at least the shape is known" case,
-- by combining ambiguous inputs using 'Semigroup' operation.
-- 
-- >>> p3 >>= lookup ["X", "Y", "Z", "W"] 
-- Just ["WZ","WZ","YX","YX"]
newtype PreNatMap f g = PreNatMap (Map (Shape f) (PosData g))

deriving instance (Eq (f Ignored), Eq (g Int)) => Eq (PreNatMap f g)
deriving instance (Ord (f Ignored), Ord (g Int)) => Ord (PreNatMap f g)

instance (Show (f Int), Show (g Int), Traversable f, Functor g) => Show (PreNatMap f g) where
  showsPrec p pnm = showsUnaryWith showsPrec "make" p (toEntries pnm)

data PosData g = PosData
  !(UV.Vector Int)
    -- ^ Vector @v@ representing LHS pattern variables.
    --
    -- Invariant (canonical reindexing):
    -- scanning @v@ left-to-right, when a value appears for the first time,
    -- it must be exactly the next fresh id (0,1,2,...).
    --
    -- More formally: let @firstOcc x@ be the least index @i@ with @v!i = x@.
    -- Then @v!(firstOcc x) == #{ y | firstOcc y < firstOcc x }@.
    --
    -- Consequences (under this invariant):
    --
    -- * If @v@ is nonempty then @v!0 == 0@.
    -- * For all indices @i@, @0 <= v!i <= i@.
    -- * If @v@ has @k@ distinct values then @maximum v == k-1@.
    -- * All elements of @v@ are pairwise distinct iff @v == [0..n-1]@
    --   (where @n = length v@). Equivalently, @n==0 || v!(n-1) == n-1@;
    --   see 'isCompleteLHS'.

  !(g Int)
    -- ^ RHS variable expression @gx@.
    --
    -- Invariant: every variable occurring in @gx@ must also occur in @v@.

deriving instance (Eq (g Int)) => Eq (PosData g)
deriving instance (Ord (g Int)) => Ord (PosData g)
deriving instance (Show (g Int)) => Show (PosData g)

-- * Entry

-- | Empty 'PreNatMap' with no knowledge.
empty :: PreNatMap f g
empty = PreNatMap Map.empty

-- | Extract @PreNatMap@ as a list of examples.
toEntries :: (Traversable f, Functor g) => PreNatMap f g -> [(f Int, g Int)]
toEntries (PreNatMap pnm) = preEntry <$> Map.toList pnm
  where
    preEntry (Shape f, PosData lhs rhs) = (fn, rhs)
      where
        fi = indices f
        fn = (lhs UV.!) <$> fi

-- | Rebuild from a list of examples
fromEntries :: (Ord (f Ignored), Eq (g Ignored), Foldable f, Traversable g, Ord a)
  => [(f a, g a)] -> Maybe (PreNatMap f g)
fromEntries = foldl' (\mm (fa, ga) -> mm >>= \ !m -> refine fa ga m) (Just empty)

-- | 'fromEntries' but raises 'error' on 'Nothing' case.
make :: (Ord (f Ignored), Eq (g Ignored), Foldable f, Traversable g, Ord a)
  => [(f a, g a)] -> PreNatMap f g
make = fromMaybe (error "make: inconsistent entries") . fromEntries

-- | Convert to 'NatMap' by discarding non-full entries
toNatMap :: (Ord (f Ignored), Traversable f, Functor g) => PreNatMap f g -> NatMap f g
toNatMap (PreNatMap pnm) = NM.fromEntries $ mapMaybe fullToEntry $ Map.toList pnm
  where
    fullToEntry (Shape f, pd@(PosData _ rhs))
      | isCompleteLHS pd = Just $ NM.unsafeMakeEntry (indices f) rhs
      | otherwise = Nothing

-- | Convert from 'NatMap'
fromNatMap :: (Traversable f, Traversable g) => NatMap f g -> PreNatMap f g
fromNatMap nm = PreNatMap $ Map.fromDistinctAscList $
  entryToPosData <$> NM.toEntries nm
    where
      entryToPosData e = (f, pd)
        where
          (f, gx) = NM.getKeyValue e
          vars = NM.makeVars (lengthShape f)
          unreachable = error "this makePosData can't fail"
          pd = fromMaybe unreachable $ makePosData vars gx

-- | Extract only the 'Shape' part as a plain 'Map'.
toShapeMap :: PreNatMap f g -> Map (Shape f) (Shape g)
toShapeMap (PreNatMap pnm) = Map.map (\ (PosData _ gi) -> Shape gi) pnm

-- | Convert the 'Map' of 'Shape' parts to @PreNatMap@, by each mapping
--   of shape @f0 :: Shape f@ to shape @g0 :: Shape g@ as an example input-output
--   pair of contentless values @(f (), g ())@.
--
--   Note that this operation can fail when @f@ is empty and @g@ is nonempty.
--   For example, a @Map@ containing mapping @Shape Nothing@ to @Shape (Just ())@
--   fails, as no natural transformation @Maybe ~> Maybe@ can turn @Nothing@ to @Just x@.
fromShapeMap :: (Foldable f, Traversable g) => Map (Shape f) (Shape g) -> Maybe (PreNatMap f g)
fromShapeMap m = PreNatMap <$> sequenceA (Map.mapWithKey makeShapePosData m)

-- | Query the output of natural transformation for given input.
--   Succeeds only when the output is uniquely determined.
match :: (Eq a, Ord (f Ignored), Foldable f, Functor g) => f a -> PreNatMap f g -> Maybe (g a)
match fa (PreNatMap pnm) = do
  pd@(PosData lhs rhs) <- Map.lookup (Shape fa) pnm
  if isCompleteLHS pd
    then pure $ makeRHS (toList fa) pd
    else do
      funLhs <- functionalRelI (zip (UV.toList lhs) (toList fa))
      let ga = (funLhs IntMap.!) <$> rhs
      pure ga

-- | Query the output of natural transformation for given input @fa :: f a@.
--   Succeeds only when the @PreNatMap@ had full knowledge for the inputs
--   with same shape to @fa@.
--
-- Compared to @match@, @fullMatch@ does not require @Eq a@ constraint
-- for the type of contents, by giving up cases which requires checks for
-- equality comparison between contents of the input @fa@. 
fullMatch :: (Ord (f Ignored), Foldable f, Functor g) => f a -> PreNatMap f g -> Maybe (g a)
fullMatch fa (PreNatMap pnm) = do
  pd <- Map.lookup (Shape fa) pnm
  if isCompleteLHS pd
    then pure $ makeRHS (toList fa) pd
    else Nothing

isFull :: (Ord (f Ignored), Foldable f, Functor g) => Shape f -> PreNatMap f g -> Bool
isFull f (PreNatMap pnm) = maybe False isCompleteLHS $ Map.lookup f pnm

-- | Query the output of natural transformation for given input @fa :: f a@.
--   Succeeds if the shape of the output corresponding to the input
--   is known.
--
--   'lookup' succeeds even if the output is not determined uniquely.
--   If there are multiple contents of inputs for a content of the output,
--   'lookup' merges all of the candidate contents using 'Semigroup' operation.
lookup :: (Semigroup a, Ord (f Ignored), Foldable f, Functor g) => f a -> PreNatMap f g -> Maybe (g a)
lookup = lookupWith id

-- | Query the output of natural transformation for given input @fa :: f a@,
--   while mapping its contents to another type @b@ with a @Semigroup@ instance.
--
-- > lookupWith h fa === lookup (h <$> fa)
lookupWith :: (Semigroup b, Ord (f Ignored), Foldable f, Functor g) => (a -> b) -> f a -> PreNatMap f g -> Maybe (g b)
lookupWith h fa (PreNatMap pnm) = do
  pd@(PosData lhs rhs) <- Map.lookup (Shape fa) pnm
  let bs = h <$> toList fa
      funLhs = IntMap.fromListWith (<>) (zip (UV.toList lhs) bs)
      gb | isCompleteLHS pd = makeRHS bs pd
         | otherwise = (funLhs IntMap.!) <$> rhs
  pure gb

-- | Looks up only the shape.
--
-- @
-- lookupShape (Shape f) p === Shape '<$>' lookup ('Data.Functor.void' f) p
-- @
lookupShape :: Ord (f Ignored) => Shape f -> PreNatMap f g -> Maybe (Shape g)
lookupShape f (PreNatMap pnm) = case Map.lookup f pnm of
  Nothing -> Nothing
  Just (PosData _ rhs) -> Just (Shape rhs)

-- | Refines knowledge a 'PreNatMap' contains by a pair of example
--   input-output pair.
--
-- Returns @Nothing@ if the given example is not consistent with the already given
-- examples.
refine :: (Ord a, Ord (f Ignored), Eq (g Ignored), Foldable f, Traversable g) => f a -> g a -> PreNatMap f g -> Maybe (PreNatMap f g)
refine fa ga (PreNatMap pnm) = case Map.lookup (Shape fa) pnm of
  -- Create new entry
  Nothing -> do
    pd <- makePosData (toList fa) ga
    pure $ PreNatMap $ Map.insert (Shape fa) pd pnm
  -- Update exising entry
  Just pd -> do
    pd' <- refinePosData pd (toList fa) ga
    pure $ PreNatMap $ Map.insert (Shape fa) pd' pnm

-- | 'refine' but only the shapes of the input and output is given.
refineShape :: (Ord (f Ignored), Eq (g Ignored), Foldable f, Traversable g)
  => Shape f -> Shape g -> PreNatMap f g -> Maybe (PreNatMap f g)
refineShape f g (PreNatMap pnm) = case Map.lookup f pnm of
  -- Create new entry
  Nothing -> do
    pd <- makeShapePosData f g
    pure $ PreNatMap $ Map.insert f pd pnm
  -- Check existing entry has the matcing shape 
  Just (PosData _ gx) -> PreNatMap pnm <$ guard (g == Shape gx)

---- Utilities ----

-- | Tests if the "lhs" vector of @PosData@ contains
--   all distinct values.
--
--   By the invariant of @PosData@, it is not necessary
--   to check every element.
isCompleteLHS :: PosData g -> Bool
isCompleteLHS (PosData lhs _) = n == 0 || lhs UV.! (n - 1) == (n - 1)
  where
    n = UV.length lhs

-- | Creates RHS ignoring LHS variable pattern,
--   assuming 'isCompleteLHS' hold.
makeRHS :: Functor g => [a] -> PosData g -> g a
makeRHS as (PosData _ gi) =
  let aVec = V.fromList as
  in (aVec V.!) <$> gi

-- Create an IntMap if the relation is functional
functionalRelI :: (Eq a) => [(Int, a)] -> Maybe (IntMap.IntMap a)
functionalRelI = loop IntMap.empty
  where
    loop !m [] = pure m
    loop !m ((k,v) : rest) = case IntMap.lookup k m of
      Nothing -> loop (IntMap.insert k v m) rest
      Just v'
        | v == v' -> loop m rest
        | otherwise -> Nothing

makeShapePosData :: (Foldable f, Traversable g)
  => Shape f -> Shape g -> Maybe (PosData g)
makeShapePosData (Shape f) (Shape g)
  | null f && not (null g) = Nothing
  | otherwise = Just $ PosData lhs rhs
  where
    lhs = UV.replicate (length f) 0
    rhs = 0 <$ g

-- >>> makePosData "foo" "bar"
-- Nothing
-- >>> makePosData "banana" "anba"
-- Just (PosData [0,1,2,1,2,1] [1,2,0,1])
-- >>> makePosData "banana" (Just 'b')
-- Just (PosData [0,1,2,3,4,5] (Just 0))
makePosData :: (Ord a, Traversable g) => [a] -> g a -> Maybe (PosData g)
makePosData as ga = PosData lhs <$> rhs
  where
    rhsSet = Set.fromList (toList ga)
    (lhsList, revmap) = reindex (`Set.member` rhsSet) as
    lhs = UV.fromList lhsList
    rhs = traverse (`Map.lookup` revmap) ga

refinePosData :: (Ord a, Eq (g Ignored), Traversable g) => PosData g -> [a] -> g a -> Maybe (PosData g)
refinePosData (PosData lhs rhs) as ga = do
  ga' <- zipMatch rhs ga
  pd@(PosData lhs' _) <- makePosData (zip (UV.toList lhs) as) ga'
  guard $ UV.length lhs == UV.length lhs'
  pure pd

reindex :: (Ord a) => (a -> Bool) -> [a] -> ([Int], Map a Int)
reindex mask = loop 0 Map.empty
  where
    loop _ rev [] = ([], rev)
    loop !n !rev (a : rest)
      | mask a = case Map.lookup a rev of
          Nothing -> case loop (n + 1) (Map.insert a n rev) rest of
            ~(ks,rev') -> (n : ks, rev')
          Just k  -> case loop n rev rest of
            ~(ks,rev') -> (k : ks, rev')
      | otherwise = case loop (n + 1) rev rest of
            ~(ks,rev') -> (n : ks, rev')
