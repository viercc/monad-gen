{-# LANGUAGE RankNTypes #-}

module Isomorphism(
    Iso(..),
    makePositionIsoFactors,
    makeShapeIsoFactors
) where

import qualified Data.LazyVec as Vec
import qualified Data.Vector as V

import qualified Data.Map as Map
import Data.PTraversable
import Data.PTraversable.Extra
import NatMap (NatMap)
import qualified NatMap
import Data.Functor (void)
import Data.Maybe (mapMaybe)

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
makePositionIsoFactors = filter nonTrivial $ positionShufflesOf <$> shapes

positionShufflesOf :: PTraversable f => f () -> [Iso f]
positionShufflesOf f_ = do
    let n = _length f_
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
    if eqDefault f_ (void fa)
        then mk (V.fromList (_toList fa))
        else fa

makeShapeIsoFactors :: (PTraversable f) => [[Iso f]]
makeShapeIsoFactors = map (mapMaybe buildIso . adjacents) groups
    where
        ss = V.fromList shapes
        lens = _length <$> ss
        ks = [ 0 .. length ss - 1 ]
        idNat = NatMap.identity
        groupsMap = Map.fromListWith Map.union [(lens V.! k, Map.singleton k k) | k <- ks]
        groups = map Map.elems . filter nonTrivial $ Map.elems groupsMap
        buildIso (j,k) =
            let fj = ss V.! j
                fk = ss V.! k
                nt = insertSym fj fk . insertSym fk fj $ idNat
            in NatMap.toTotal nt Nothing $ \g -> Just (Iso g g)

adjacents :: [b] -> [(b,b)]
adjacents bs = zip bs (drop 1 bs)

insertSym :: (PTraversable f) => f () -> f () -> NatMap f f -> NatMap f f
insertSym fKey fVal = NatMap.alter (\as _ -> tryFillUp as fVal) (NatMap.key fKey)

tryFillUp :: (PTraversable f) => Vec.Vec a -> f b -> Maybe (f a)
tryFillUp as f = traverseDefault (as Vec.!?) (_indices f)