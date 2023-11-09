{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Data.PTraversable.Extra(
  Vec,

  toVec, cache,
  skolem, skolem2, skolem3,
  vecSkolem,
  eqDefault,
  shapes,

  _toList, _length, _all, _indices
) where

import           Data.Coerce

import           Data.Monoid (Sum(..), Endo (..), All (..))
import           Data.Functor.Const
import           Control.Monad.State

import           GHC.Generics           ((:.:) (..))

import           Data.LazyVec (Vec)
import qualified Data.LazyVec as Vec
import           Data.PTraversable

type Fresh = State Int

fresh :: Fresh Int
fresh = state (\i -> (i, i+1))

runFresh :: Fresh a -> a
runFresh fa = evalState fa 0

var :: (Vec :.: State Int) Int
var = Comp1 $ Vec.singleton fresh

var_ :: (Vec :.: Const (Sum Int)) a
var_ = Comp1 $ Vec.singleton (Const (Sum 1))

skolem :: forall m. (PTraversable m) => Vec (m Int)
skolem = fmap runFresh . unComp1 $ enum1 var

-- | vecSkolem = fmap toVec . skolem
vecSkolem :: forall m proxy. (PTraversable m) => proxy m -> Vec (Vec Int)
vecSkolem _ = fmap (Vec.iota . getSum . getConst) . unComp1 $ enum1 @m var_ 

skolem2 :: forall m. (PTraversable m) => Vec (m (m Int))
skolem2 = fmap unComp1 (skolem @(m :.: m))

skolem3 :: forall m. (PTraversable m) => Vec (m (m (m Int)))
skolem3 = fmap (fmap unComp1 . unComp1) (skolem @(m :.: m :.: m))

eqDefault :: forall f a. (PTraversable f, Eq a) => f a -> f a -> Bool
eqDefault = coerce ((==) @(WrappedPTraversable f a))

shapes :: forall f. (PTraversable f) => [f ()]
shapes = enum1 [()]

cache :: Vec a -> Vec a
cache = Vec.fromVector . Vec.toVector

toVec :: PTraversable t => t a -> Vec a
toVec = Vec.vec . _toList

_toList :: PTraversable t => t a -> [a]
_toList = ($ []) . appEndo . foldMapDefault (Endo . (:))

_length :: PTraversable t => t a -> Int
_length = getSum . foldMapDefault (const 1)

_all :: PTraversable t => (a -> Bool) -> t a -> Bool
_all p = getAll . foldMapDefault (All . p)

_indices :: PTraversable t => t a -> t Int
_indices = runFresh . traverseDefault (const fresh)
