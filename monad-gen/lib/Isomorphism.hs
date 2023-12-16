{-# LANGUAGE RankNTypes #-}

module Isomorphism(
    Iso(..),
    makePositionIsoFactors,
    makeShapeIsoFactors
) where

import qualified Data.Vector as V

import qualified Data.Map as Map
import Data.PTraversable
import Data.PTraversable.Extra

import Data.NatMap (NatMap)
import qualified Data.NatMap as NatMap
import Data.Functor (void)
import Data.Maybe (mapMaybe)
import Data.Foldable (toList)

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

makePositionIsoFactors :: PTraversable f => [[Iso f]]
makePositionIsoFactors = filter (not . null) $ positionShufflesOf <$> shapes

positionShufflesOf :: PTraversable f => f () -> [Iso f]
positionShufflesOf f_ = do
    let n = length f_
        fk = _indices f_
    k <- [0 .. n - 2]
    let fk' = fmap (tp k) fk
        iso = shuffleNatAt f_ (\as -> (as V.!) <$> fk')
    pure $ Iso iso iso

tp :: Int -> Int -> Int
tp k x
  | x == k     = k + 1
  | x == k + 1 = k
  | otherwise  = x

shuffleNatAt :: PTraversable f => f () -> (forall b. V.Vector b -> f b) -> f a -> f a
shuffleNatAt f_ mk fa =
    if f_ == void fa
        then mk (V.fromList (toList fa))
        else fa

makeShapeIsoFactors :: (PTraversable f) => [[Iso f]]
makeShapeIsoFactors = map (mapMaybe buildIso . adjacents) groups
    where
        ss = V.fromList shapes
        lens = length <$> ss
        ks = [ 0 .. length ss - 1 ]
        idNat = NatMap.identity
        groupsMap = Map.fromListWith Map.union [(lens V.! k, Map.singleton k k) | k <- ks]
        groups = map Map.elems . filter nonTrivial $ Map.elems groupsMap
        buildIso (j,k) =
            let fj = ss V.! j
                fk = ss V.! k
                nt = insertSym fj fk . insertSym fk fj $ idNat
            in (\(NatMap.NT g) -> Iso g g) <$> NatMap.toTotal nt

adjacents :: [b] -> [(b,b)]
adjacents bs = zip bs (drop 1 bs)

insertSym :: (PTraversable f) => f () -> f () -> NatMap f f -> NatMap f f
insertSym fKey fVal = case NatMap.makeEntry (_indices fKey) (_indices fVal) of
    Nothing -> id
    Just e -> NatMap.insert e
