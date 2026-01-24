{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RoleAnnotations     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
module Data.NatMap (
    NatMap(),

    -- * Entry
    Entry(),
    getKeyValue,
    makeEntry,
    makeIdEntry,
    unsafeMakeEntry,
    bimapEntry,

    -- * Construction
    empty, singleton,
    partialIdentity,
    fromEntries,
    insert, delete,
    
    -- * Queries
    size,
    member, notMember,
    lookup, lookup_,
    keys,
    toEntries,

    -- * Map, Filter, Traversal

    map1, mapMaybe1, traverse1, wither1,
    mapWithKey1, mapMaybeWithKey1, traverseWithKey1, witherWithKey1,

    -- * Combinators

    union, unionWith, consistentUnion,

    -- * As partial natural transformation

    identity, compose,
    outerNat, innerNat, horizontalCompose,

    -- * Totality

    fullSize, isTotal,
    toTotal,

    -- * Re-exports
    (:~>)(..), wrapNT, unwrapNT,

    -- * Utility
    Var(), makeVars, indices,
) where

import Prelude hiding (lookup)

import Data.Kind ( Type )

import Data.Proxy ( Proxy(..) )
import Data.Maybe (fromMaybe)
import Data.Functor.Compose (Compose (..))

import Data.Foldable(toList)
import Data.Coerce (coerce)

import qualified Data.Map.Lazy as Map
import qualified Data.Map.Merge.Lazy as Map
import qualified Data.Vector as V

import Data.PTraversable

import Data.FunctorShape

import Control.Natural

import qualified TraversableUtil

-- | Data structure which represents partial natural transformations,
--   like usual 'Map' which represents partial functions.
--
-- @'Map' k v@ can be seen as a partial function.
--
-- @
-- m :: Map k v
-- (\k -> Data.Map.lookup k m) :: k -> Maybe v
-- @
-- 
-- Analogically, a @'NatMap' f g@ can be seen as a partial natural transformation,
-- in the same sense @Map@ represents a partial function.
-- 
-- @
-- nm :: NatMap f g
-- (\fa -> 'lookup' fa nm) :: forall a. f a -> Maybe (g a)
-- @
-- 
newtype NatMap (f :: Type -> Type) (g :: Type -> Type)
  = Mk (Map.Map (Shape f) (g Var))
type role NatMap nominal representational

deriving instance (WeakEq f, Eq (g Var)) => Eq (NatMap f g)
deriving instance (WeakOrd f, Ord (g Var)) => Ord (NatMap f g)

-- * Entry

data Entry f g = Entry (Shape f) (g Var)

deriving instance (Show (f Ignored), Show (g Var)) => Show (Entry f g)
deriving instance (WeakEq f, Eq (g Var)) => Eq (Entry f g)
deriving instance (WeakOrd f, Ord (g Var)) => Ord (Entry f g)

getKeyValue :: Entry f g -> (Shape f, g Var)
getKeyValue (Entry fx gx) = (fx, gx)

bimapEntry :: (Shape f -> Shape f') -> (forall x. g x -> g' x) -> Entry f g -> Entry f' g'
bimapEntry ff gg (Entry f gi) = Entry (ff f) (gg gi)

makeEntry :: (Traversable f, Traversable g, Ord k) => f k -> g k -> Maybe (Entry f g)
makeEntry fk gk =
  do table <- makeKeyTable (toList fk)
     gx <- traverse (\k -> Map.lookup k table) gk
     pure (Entry (Shape fk) gx)

makeIdEntry :: (Traversable f) => f k -> Entry f f
makeIdEntry fk = Entry (Shape fk) (indices (Shape fk))

makeKeyTable :: Ord k => [k] -> Maybe (Map.Map k Var)
makeKeyTable ks
  | n == Map.size table = Just table
  | otherwise = Nothing
  where
    n = length ks
    table = Map.fromList (zip ks (Var <$> [0..]))

unsafeMakeEntry :: (Traversable f, Functor g, Ord k) => f k -> g k -> Entry f g
unsafeMakeEntry fk gk =
  case makeKeyTable (toList fk) of
    Just table -> Entry (Shape fk) ((table Map.!) <$> gk)
    Nothing -> error "bad LHS functor!"

-- * Construction

empty :: NatMap f g
empty = Mk Map.empty

singleton :: Entry f g -> NatMap f g
singleton (Entry f1 gx) = Mk $ Map.singleton f1 gx

partialIdentity :: (WeakOrd f, Traversable f) => [f a] -> NatMap f f
partialIdentity fShapes = Mk $ Map.fromList [ (Shape f1, indices (Shape f1)) | f1 <- fShapes ]

fromEntries :: (WeakOrd f) => [Entry f g] -> NatMap f g
fromEntries es = Mk $ Map.fromList (getKeyValue <$> es)

insert :: WeakOrd f => Entry f g -> NatMap f g -> NatMap f g
insert (Entry f1 gx) (Mk m) = Mk $ Map.insert f1 gx m

delete :: WeakOrd f => f any -> NatMap f g -> NatMap f g
delete fx (Mk m) = Mk $ Map.delete (Shape fx) m

-- * Queries

size :: NatMap f g -> Int
size (Mk m) = Map.size m

member, notMember :: WeakOrd f => f a -> NatMap f g -> Bool
member fa (Mk m) = Map.member (Shape fa) m
notMember fa = not . member fa

lookup :: (WeakOrd f, Foldable f, Functor g) => f a -> NatMap f g -> Maybe (g a)
lookup fa (Mk m) = fmap (V.unsafeIndex as . unVar) <$> Map.lookup (Shape fa) m
  where
    as = V.fromList (toList fa)

lookup_ :: (WeakOrd f, Functor g) => Shape f -> NatMap f g -> Maybe (g Var)
lookup_ f1 (Mk m) = Map.lookup f1 m

keys :: NatMap f g -> [Shape f]
keys (Mk m) = Map.keys m

toEntries :: NatMap f g -> [Entry f g]
toEntries (Mk m) = [ Entry f1 gx | (f1, gx) <- Map.toAscList m ]

-- keysSet :: NatMap f g -> ShapeSet f

-- * Mapping, Filtering, Traversing

map1 :: (forall a. g a -> h a) -> NatMap f g -> NatMap f h
map1 gh (Mk m) = Mk (Map.map gh m)

mapMaybe1 :: (forall a. g a -> Maybe (h a)) -> NatMap f g -> NatMap f h
mapMaybe1 gh (Mk m) = Mk (Map.mapMaybe gh m)

traverse1 :: Applicative m => (forall a. g a -> m (h a)) -> NatMap f g -> m (NatMap f h)
traverse1 gh (Mk m) = Mk <$> traverse gh m

wither1 :: Applicative m => (forall a. g a -> m (Maybe (h a))) -> NatMap f g -> m (NatMap f h)
wither1 gh (Mk m) = Mk . Map.mapMaybe id <$> traverse gh m

mapWithKey1 :: Traversable f => (forall a. Ord a => f a -> g a -> h a) -> NatMap f g -> NatMap f h
mapWithKey1 fgh (Mk m) = Mk $ Map.mapWithKey (\f1 gx -> fgh (indices f1) gx) m

mapMaybeWithKey1 :: Traversable f => (forall a. Ord a => f a -> g a -> Maybe (h a)) -> NatMap f g -> NatMap f h
mapMaybeWithKey1 fgh (Mk m) = Mk $ Map.mapMaybeWithKey (\f1 gx -> fgh (indices f1) gx) m

traverseWithKey1 :: (Traversable f, Applicative m) => (forall a. Ord a => f a -> g a -> m (h a)) -> NatMap f g -> m (NatMap f h)
traverseWithKey1 fgh (Mk m) = Mk <$> Map.traverseWithKey (\f1 gx -> fgh (indices f1) gx) m

witherWithKey1 :: (Traversable f, Applicative m) => (forall a. Ord a => f a -> g a -> m (Maybe (h a))) -> NatMap f g -> m (NatMap f h)
witherWithKey1 fgh (Mk m) = Mk . Map.mapMaybe id <$> Map.traverseWithKey (\f1 gx -> fgh (indices f1) gx) m

-- * Combinators

union :: forall f g. (WeakOrd f) => NatMap f g -> NatMap f g -> NatMap f g
union = coerce (Map.union @(Shape f) @(g Var))

unionWith :: forall f g. (WeakOrd f) => (forall a. g a -> g a -> g a) -> NatMap f g -> NatMap f g -> NatMap f g
unionWith op = coerce (Map.unionWith (op @Var))

consistentUnion :: forall f g. (WeakOrd f, Eq (g Var)) => NatMap f g -> NatMap f g -> Maybe (NatMap f g)
consistentUnion = coerce (consistentUnionImpl @(Shape f) @(g Var))

consistentUnionImpl :: forall k v. (Ord k, Eq v) => Map.Map k v -> Map.Map k v -> Maybe (Map.Map k v)
consistentUnionImpl =
  Map.mergeA
    Map.preserveMissing
    Map.preserveMissing
    (Map.zipWithAMatched (\_ v1 v2 -> if v1 == v2 then Just v1 else Nothing))

-- * Combinators as partial natural transformations

identity :: PTraversable f => NatMap f f
identity = Mk $ Map.fromList [ (f1, indices f1) | f1 <- Shape <$> enum1 [()] ]

compose :: (WeakOrd f, WeakOrd g, Foldable g, Functor h) => NatMap g h -> NatMap f g -> NatMap f h
compose nm1 nm2 = mapMaybe1 (\gx -> lookup gx nm1) nm2

outerNat :: (Traversable f, Traversable g, PTraversable h, Ord (f (h Ignored))) => NatMap f g -> NatMap (Compose f h) (Compose g h)
outerNat nm = fromEntries $
  do Entry (Shape f_) gx <- toEntries nm
     fh_ <- traverse (const hShapes) f_
     let Compose fhy = indices (Shape (Compose fh_))
         hyVec = V.fromList (toList fhy)
         ghy = (\x -> V.unsafeIndex hyVec (unVar x)) <$> gx
     pure (Entry (Shape (Compose fhy)) (Compose ghy))
  where hShapes = enum1 [()]

innerNat :: (Traversable f, Traversable g, PTraversable h, WeakOrd f) => NatMap f g -> NatMap (Compose h f) (Compose h g)
innerNat nm = fromEntries $
  do hx <- indices . Shape <$> enum1 [()]
     hEntry <- traverse (\x -> appendVar x <$> es) hx
     let hf_xy = fst <$> hEntry
         hg_xy = snd <$> hEntry
     pure $ unsafeMakeEntry (Compose hf_xy) (Compose hg_xy)
  where
    es = [ (indices f1, gy) | Entry f1 gy <- toEntries nm ]
    appendVar x (fy, gy) = ((,) x <$> fy, (,) x <$> gy)

horizontalCompose :: (Traversable f, Functor g, Traversable h, Functor j, Ord (f (h Ignored)))
  => NatMap f g -> NatMap h j -> NatMap (Compose f h) (Compose g j)
horizontalCompose fgMap hjMap = fromEntries $
  do (fx, gx) <- fgEntries
     fPairs <- traverse (\x -> appendVar x <$> hjEntries) fx
     let fh_xy = fst <$> fPairs
         fj_xy = snd <$> fPairs
         vecj_xy = V.fromList (toList fj_xy)
         gj_xy = (\x -> V.unsafeIndex vecj_xy (unVar x)) <$> gx
     pure $ unsafeMakeEntry (Compose fh_xy) (Compose gj_xy)
  where
    toPairs nm = fmap (\(Entry f1 gx) -> (indices f1, gx)) (toEntries nm)
    fgEntries = toPairs fgMap
    hjEntries = toPairs hjMap
    appendVar x (fy, gy) = ((,) x <$> fy, (,) x <$> gy)

-- * Totalities

fullSize :: forall f g. (PTraversable f) => NatMap f g -> Int
fullSize _ = cardinality1 @f Proxy 1

isTotal :: (PTraversable f) => NatMap f g -> Bool
isTotal nm = size nm == fullSize nm

toTotal :: (PTraversable f, Functor g) => NatMap f g -> Maybe (f :~> g)
toTotal nm
  | isTotal nm = Just (NT (\fx -> fromMaybe err (lookup fx nm)))
  | otherwise  = Nothing
  where
    err = error "isTotal but there's a missed key?"

-- * Utility

makeVars :: Int -> [Var]
makeVars n = Var <$> [0 .. n - 1]

indices :: Traversable f => Shape f -> f Var
indices (Shape fk) = Var <$> TraversableUtil.indices fk

-- | An opaque type representing syntactic variable.
newtype Var = Var { unVar :: Int }
  deriving (Eq, Ord)

instance Show Var where
  show (Var n) = "x" ++ show n
