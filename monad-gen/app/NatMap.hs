{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RoleAnnotations     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE StandaloneDeriving  #-}
module NatMap (
    Entry(),
    entryKey, withEntry,
    makeEntry, tryMakeEntry,

    Key(),
    key, unkey,

    NatMap(),
    size, fullSize,
    member, notMember,
    lookup, lookup_,
    isTotal, toTotal,
    keys, keysSet, entries,

    empty, identity,
    singleton,
    map1, mapMaybe1,
    fromNat, fromPartialNat,
    fromList,

    alter, update, adjust, insert,
    delete,

    union, unionWith, consistentBy,
    
    debug,
) where

import Prelude hiding (lookup)

import Data.Coerce (coerce)

import Data.Kind ( Type )
import Data.Proxy ( Proxy(..) )
import Data.Foldable(toList)
import qualified Data.IntMap.Lazy as IM

import Data.PTraversable

import Data.PTraversable.Extra
import qualified Data.LazyVec as Vec
import qualified Set1.Internal as Set1
import Set1.Internal (Key(..), unkey, key, Set1)


-- | Map representing natural transformation
--   @(forall x. f x -> g x)@ instead of usual function
newtype NatMap (f :: Type -> Type) (g :: Type -> Type)
  = Mk (IM.IntMap (g Int))
type role NatMap nominal representational

deriving instance (Eq (g Int)) => Eq (NatMap f g)
deriving instance (Ord (g Int)) => Ord (NatMap f g)

keyToSkolem :: forall f. PTraversable f => Key f -> f Int
keyToSkolem = (table Vec.!) . fromEnum
  where
     table = cache $ skolem @f
{-# INLINE keyToSkolem #-}

keyToVars :: forall f. PTraversable f => Key f -> Vec Int
keyToVars = (table Vec.!) . fromEnum
  where
     table = cache $ vecSkolem @f Proxy
{-# INLINE keyToVars #-}

fIdx :: PTraversable f => f any -> Int
fIdx = keyIdx . key

-- | An entry of @NatMap f g@
data Entry (f :: Type -> Type) (g :: Type -> Type) = MkEntry Int (g Int)
type role Entry nominal representational

deriving instance (Eq (g Int)) => Eq (Entry f g)
deriving instance (Ord (g Int)) => Ord (Entry f g)

entryKey :: Entry f g -> Key f
entryKey (MkEntry i _) = MkKey i

withEntry :: PTraversable f => Entry f g -> (forall x. Ord x => f x -> g x -> r) -> r
withEntry (MkEntry i gx) k = k (keyToSkolem (MkKey i)) gx
{-# INLINE withEntry #-}

makeEntry :: PTraversable f => Key f -> (forall x. Vec x -> g x) -> Entry f g
makeEntry k nt = MkEntry (keyIdx k) (nt $ keyToVars k)
{-# INLINE makeEntry #-}

tryMakeEntry :: PTraversable f => Key f -> (forall x. Vec x -> Maybe (g x)) -> Maybe (Entry f g)
tryMakeEntry k nt = MkEntry (keyIdx k) <$> nt (keyToVars k)
{-# INLINE tryMakeEntry #-}

-- Query --
size :: NatMap f g -> Int
size (Mk m) = IM.size m

fullSize :: forall f g. (PTraversable f) => NatMap f g -> Int
fullSize _ = size1 @f Proxy 1

isTotal :: (PTraversable f) => NatMap f g -> Bool
isTotal nm = size nm == fullSize nm

member, notMember :: (PTraversable f) => Key f -> NatMap f g -> Bool
member k (Mk m) = IM.member (keyIdx k) m
notMember k = not . member k

lookup :: (PTraversable f, Functor g) => f a -> NatMap f g -> Maybe (g a)
lookup fa (Mk m) = fmap (toVec fa Vec.!) <$> IM.lookup (fIdx fa) m

lookup_ :: (PTraversable f, Functor g) => Key f -> NatMap f g -> Maybe (g ())
lookup_ k (Mk m) = fmap (() <$) $ IM.lookup (keyIdx k) m

keys :: NatMap f g -> [Key f]
keys (Mk m) = MkKey <$> IM.keys m

keysSet :: NatMap f g -> Set1 f
keysSet (Mk m) = Set1.Mk (IM.keysSet m)

entries :: NatMap f g -> [Entry f g]
entries (Mk m) = uncurry MkEntry <$> IM.toList m

toTotal :: (PTraversable f, Functor g) => NatMap f g -> r -> ((forall a. f a -> g a) -> r) -> r
toTotal nm@(Mk m) failCase justCase
  | isTotal nm = justCase fg
  | otherwise  = failCase
  where fg fa = let content = toVec fa
                    gx = m IM.! fIdx fa
                in content `seq` (content Vec.!) <$> gx

-- Construct --
empty :: NatMap f g
empty = Mk IM.empty

identity :: (PTraversable f) => NatMap f f
identity = Mk . IM.fromList . toList . Vec.indexed $ skolem

singleton :: Entry f g -> NatMap f g
singleton (MkEntry i gx) = Mk (IM.singleton i gx)

map1 :: (forall a. g a -> h a) -> NatMap f g -> NatMap f h
map1 gh (Mk m) = Mk (gh <$> m)

mapMaybe1 :: (forall a. g a -> Maybe (h a)) -> NatMap f g -> NatMap f h
mapMaybe1 gh' (Mk m) = Mk (IM.mapMaybe gh' m)

fromNat :: (PTraversable f)
        => (forall a. f a -> g a) -> NatMap f g
fromNat fg = map1 fg identity

fromPartialNat :: (PTraversable f)
               => (forall a. f a -> Maybe (g a)) -> NatMap f g
fromPartialNat fg' = mapMaybe1 fg' identity

fromList :: (PTraversable f)
         => [Entry f g] -> NatMap f g
fromList es = Mk $
  IM.fromList [ (i, gi) | MkEntry i gi <- es ]

-- Update --
wrapUpdator
  :: forall f g.
     (PTraversable f)
  => (Vec Int -> Int -> IM.IntMap (g Int) -> IM.IntMap (g Int))
  -> Key f
  -> NatMap f g -> NatMap f g
wrapUpdator updator k (Mk m) = Mk (updator (keyToVars k) (keyIdx k) m)

alter :: forall f g.
          (PTraversable f)
       => (forall a. Vec a -> Maybe (g a) -> Maybe (g a))
       -> Key f -> NatMap f g -> NatMap f g
alter updator = wrapUpdator $ \arg -> IM.alter (updator arg)

update :: forall f g.
           (PTraversable f)
        => (forall a. Vec a -> g a -> Maybe (g a))
        -> Key f -> NatMap f g -> NatMap f g
update updator = wrapUpdator $ \arg -> IM.update (updator arg)

adjust :: forall f g.
           (PTraversable f)
        => (forall a. Vec a -> g a -> g a)
        -> Key f -> NatMap f g -> NatMap f g
adjust updator = wrapUpdator $ \arg -> IM.adjust (updator arg)

insert :: forall f g.
           (PTraversable f)
        => (forall a. Vec a -> g a)
        -> Key f -> NatMap f g -> NatMap f g
insert updator = wrapUpdator $ \arg i -> IM.insert i (updator arg)

delete :: forall f g.
          (PTraversable f)
       => Key f -> NatMap f g -> NatMap f g
delete = coerce (IM.delete @(g Int))

union :: forall f g. NatMap f g -> NatMap f g -> NatMap f g
union = coerce (IM.union @(g Int))

unionWith :: forall f g. (forall a. g a -> g a -> g a) -> NatMap f g -> NatMap f g -> NatMap f g
unionWith op = coerce (IM.unionWith (op @Int))

consistentBy :: (forall a. Eq a => g a -> g a -> Bool) -> NatMap f g -> NatMap f g -> Bool
consistentBy eq (Mk m1) (Mk m2) = and $ IM.intersectionWith eq m1 m2

-- Debug --

debug :: forall f g.
         (Show (f Int),   Show (g Int),
          PTraversable f, PTraversable g)
      => NatMap f g -> String
debug (Mk m) =
  let args = skolem @f
      strs = fmap show args
      maxLen = maximum (length <$> strs)
      mkRhs fx = validate fx <$> IM.lookup (fIdx fx) m
      validate fx gx = (all (\x -> 0 <= x && x < length fx) gx, gx)
      prettyRhs Nothing = "undefined"
      prettyRhs (Just (v, gx)) = (if v then "" else "<invalid>") ++ show gx
      mkLine arg rhs = arg ++ replicate (maxLen - length arg) ' '
                       ++ " -> " ++ prettyRhs rhs
  in unlines . toList $ Vec.zipWith mkLine strs (mkRhs <$> args)
