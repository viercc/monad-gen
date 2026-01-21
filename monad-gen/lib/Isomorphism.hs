{-# LANGUAGE RankNTypes #-}

module Isomorphism(
    Iso(..),
    makePositionIso,
    makePositionIsoFactors,
    makeShapeIso,
    makeShapeIsoFactors
) where

import Data.List (permutations)
import Data.Functor (void)
import Data.Maybe (mapMaybe)
import Data.Foldable (toList)

import qualified Data.Vector as V
import qualified Data.Map as Map
import Data.PTraversable

import Data.PTraversable.Extra (shapes)
import Data.Traversable.Extra

import Data.NatMap (NatMap)
import qualified Data.NatMap as NatMap

data Iso f = Iso
  { iso1 :: forall a. f a -> f a,
    iso2 :: forall a. f a -> f a
  }

instance Semigroup (Iso f) where
    Iso f g <> Iso f' g' = Iso (f . f') (g' . g)

instance Monoid (Iso f) where
    mempty = Iso id id

nonTrivial :: Foldable f => f a -> Bool
nonTrivial as = length as > 1

makePositionIso :: PTraversable f => [[Iso f]]
makePositionIso = result
  where
    result = filter nonTrivial $ positionShufflesOf <$> shapes

positionShufflesOf :: PTraversable f => f () -> [Iso f]
positionShufflesOf f_ = do
    let n = length f_
        fk = indices f_
    perm <- V.fromListN n <$> permutations [0 .. n - 1]
    let perm' = V.backpermute (V.generate n id) perm
        fs = (perm V.!) <$> fk
        fs' = (perm' V.!) <$> fk
    pure $ Iso (shuffleNatAt fs) (shuffleNatAt fs')

makePositionIsoFactors :: PTraversable f => [[Iso f]]
makePositionIsoFactors = filter (not . null) $ positionTranspositionsOf <$> shapes

positionTranspositionsOf :: PTraversable f => f () -> [Iso f]
positionTranspositionsOf f_ = do
    let n = length f_
        fk = indices f_
    k <- [0 .. n - 2]
    let fk' = fmap (tp k) fk
        iso = shuffleNatAt fk'
    pure $ Iso iso iso

tp :: Int -> Int -> Int
tp k x
  | x == k     = k + 1
  | x == k + 1 = k
  | otherwise  = x

shuffleNatAt :: PTraversable f => f Int -> f a -> f a
shuffleNatAt fk fa =
    if void fk == void fa
        then let as = V.fromList (toList fa)
             in (as V.!) <$> fk
        else fa

makeShapeIso :: (PTraversable f) => [[Iso f]]
makeShapeIso = result
  where
    idNat = NatMap.identity
    permAssocs as = [ zip as pas | pas <- permutations as ]
    buildIso pAssocs = do
        let nt = foldl' (\m (fj, fk) -> insertSym fj fk m) idNat pAssocs
            nt' = foldl' (\m (fj, fk) -> insertSym fk fj m) idNat pAssocs
        g <- NatMap.toTotal nt
        g' <- NatMap.toTotal nt'
        pure $ Iso (g NatMap.$$) (g' NatMap.$$)
    result = map (mapMaybe buildIso . permAssocs) $ filter nonTrivial $ groupByLength shapes

makeShapeIsoFactors :: (PTraversable f) => [[Iso f]]
makeShapeIsoFactors = map (mapMaybe buildIso . adjacents) $ groupByLength shapes
    where
        idNat = NatMap.identity
        buildIso (fj,fk) =
            let nt = insertSym fj fk . insertSym fk fj $ idNat
            in (\(NatMap.NT g) -> Iso g g) <$> NatMap.toTotal nt

groupByLength :: Foldable f => [f a] -> [[f a]]
groupByLength fs = Map.elems groupsMap
  where
    groupsMap = Map.fromListWith (++) [ (length fa, [fa]) | fa <- fs ]

adjacents :: [b] -> [(b,b)]
adjacents bs = zip bs (drop 1 bs)

insertSym :: (PTraversable f) => f () -> f () -> NatMap f f -> NatMap f f
insertSym fKey fVal = case NatMap.makeEntry (indices fKey) (indices fVal) of
    Nothing -> id
    Just e -> NatMap.insert e
