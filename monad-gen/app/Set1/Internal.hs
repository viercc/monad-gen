{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RoleAnnotations     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE StandaloneDeriving  #-}
module Set1.Internal (
    Key(..),
    unkey, key,
    
    Set1(..),
    empty, singleton, full,
    fromList, fromList',
    
    insert, delete,
    union, intersection, difference, (\\),

    null, size, isFull,
    member, notMember, member', notMember',
    toList, toList',
) where

import Prelude hiding (null)

import Data.Coerce

import Data.Kind ( Type )
import Data.Proxy ( Proxy(..) )

import qualified Data.IntSet as IS

import Data.Functor.Contravariant.Divisible (Divisible(..))
import Data.PTraversable

import qualified Data.LazyVec as Vec
import Data.ContraVec(getIndex)

-- | @Key f@ is isomorphic to @f ()@ if @f ()@ take
--   finite number of values.
newtype Key (f :: Type -> Type) = MkKey { keyIdx :: Int }
   deriving (Eq, Ord)
type role Key nominal

instance (PTraversable f, Show (f ())) => Show (Key f) where
  showsPrec p k = showParen (p > 10) $ ("key " ++) . showsPrec 11 (unkey k)

instance PTraversable f => Bounded (Key f) where
   minBound = MkKey 0
   maxBound = MkKey (cardinality1 @f Proxy 1 - 1)

instance PTraversable f => Enum (Key f) where
   fromEnum = keyIdx
   toEnum =
      let MkKey m = maxBound @(Key f)
          err i = error $ "Enum (Key f): out of bounds " ++ show i ++ " in 0.." ++ show m
      in \i -> if 0 <= i && i <= m then MkKey i else err i

unkey :: PTraversable f => Key f -> f ()
unkey = (enum1 (Vec.singleton ()) Vec.!) . keyIdx
{-# INLINE unkey #-}

key :: forall f a. PTraversable f => f a -> Key f
key = MkKey . getIndex (coenum1 @f conquer)
{-# INLINE key #-}

-- | Set of @f ()@
newtype Set1 (f :: Type -> Type) = Mk IS.IntSet
  deriving (Eq, Ord)
type role Set1 nominal

instance (PTraversable f, Show (f ())) => Show (Set1 f) where
  showsPrec p s = showParen (p > 10) $ ("fromList' " ++) . showsPrec 11 (toList' s)

-- * Construction
empty :: Set1 f
empty = Mk IS.empty

singleton :: Key f -> Set1 f
singleton = coerce IS.singleton

full :: forall f. PTraversable f => Set1 f
full = Mk $ IS.fromDistinctAscList $ map keyIdx ([minBound .. maxBound] :: [Key f])

fromList :: [Key f] -> Set1 f
fromList = coerce IS.fromList

fromList' :: PTraversable f => [f any] -> Set1 f
fromList' = fromList . map key

-- * Modification
insert, delete :: Key f -> Set1 f -> Set1 f
insert = coerce IS.insert
delete = coerce IS.delete

union, intersection, difference, (\\) :: Set1 f -> Set1 f -> Set1 f
union = coerce IS.union
intersection = coerce IS.intersection
difference = coerce IS.difference
(\\) = difference

infixl 9 \\

-- * Queries
null :: Set1 f -> Bool
null = coerce IS.null

size :: Set1 f -> Int
size = coerce IS.size

isFull :: forall f. PTraversable f => Set1 f -> Bool
isFull s = size s == keyIdx (maxBound :: Key f)

member, notMember :: Key f -> Set1 f -> Bool
member = coerce IS.member
notMember = coerce IS.notMember

member', notMember' :: PTraversable f => f any -> Set1 f -> Bool
member' = member . key
notMember' = notMember . key

toList :: Set1 f -> [Key f]
toList = coerce IS.toList

toList' :: PTraversable f => Set1 f -> [f ()]
toList' = map unkey . toList
