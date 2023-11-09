{-# LANGUAGE RankNTypes #-}

module Isomorphism(
    Iso(..),
    makePositionIsoFactors,
    makeShapeIsoFactors
) where

import qualified Data.LazyVec as Vec
import qualified Data.Vector as V

import Data.List (permutations)
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
makePositionIsoFactors = filter nonTrivial $ map positionShufflesOf shapes

positionShufflesOf :: PTraversable f => f () -> [Iso f]
positionShufflesOf f_ = do
    let n = _length f_
        ks = V.generate n id
        fk = _indices f_
    g <- V.fromList <$> permutations (V.toList ks)
    let gInv = V.backpermute ks g
    pure $ Iso {
        iso1 = shuffleNatAt f_ (\as -> (V.backpermute as g V.!) <$> fk),
        iso2 = shuffleNatAt f_ (\as -> (V.backpermute as gInv V.!) <$> fk)
    }

shuffleNatAt :: PTraversable f => f () -> (forall b. V.Vector b -> f b) -> f a -> f a
shuffleNatAt f_ mk fa =
    if eqDefault f_ (void fa)
        then mk (V.fromList (_toList fa))
        else fa

makeShapeIsoFactors :: (PTraversable f) => [[Iso f]]
makeShapeIsoFactors = map (mapMaybe buildIso . shuf) groups
    where
        ss = V.fromList shapes
        lens = _length <$> ss
        ks = [ 0 .. length ss - 1 ]
        idNat = NatMap.identity
        groupsMap = Map.fromListWith Map.union [(lens V.! k, Map.singleton k k) | k <- ks]
        groups = filter nonTrivial $ Map.elems groupsMap
        buildIso s =
            let nt1 = NatMap.union (symToNat (ss V.!) s) idNat
                nt2 = NatMap.union (symToNat (ss V.!) (invertSym s)) idNat
            in NatMap.toTotal nt1 Nothing $ \g ->
                 NatMap.toTotal nt2 Nothing $ \h ->
                   Just (Iso g h)

type Sym k = Map.Map k k

shuf :: (Ord j) => Sym j -> [Sym j]
shuf s = [Map.fromAscList (zip js js') | js' <- permutations js]
    where
    js = Map.keys s

invertSym :: (Ord k) => Sym k -> Sym k
invertSym s = Map.fromList [(k, j) | (j, k) <- Map.toList s]

symToNat :: (PTraversable f) => (k -> f ()) -> Sym k -> NatMap f f
symToNat toF = Map.foldrWithKey (\k1 k2 m -> insertSym (toF k1) (toF k2) m) NatMap.empty

insertSym :: (PTraversable f) => f () -> f () -> NatMap f f -> NatMap f f
insertSym fKey fVal = NatMap.alter (\as _ -> tryFillUp as fVal) (NatMap.key fKey)

tryFillUp :: (PTraversable f) => Vec.Vec a -> f b -> Maybe (f a)
tryFillUp as f = traverseDefault (as Vec.!?) (_indices f)