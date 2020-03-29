{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Data.PTraversable.Extra where

import           Data.Coerce

import           Data.Foldable
import           Control.Monad.State

import           GHC.Generics           ((:.:) (..))

import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Contravariant.CoNumbering
import qualified Data.Functor.Numbering as Vec
import           Data.PTraversable


type Vec = Vec.FromN

var :: (Vec :.: State Int) Int
var = Comp1 $ Vec.singleton (state (\i -> (i, i+1)))

skolem :: forall m. (PTraversable m) => Vec (m Int)
skolem = fmap fillIn . unComp1 $ enum1 var
  where fillIn mx = evalState mx 0

skolem2 :: forall m. (PTraversable m) => Vec (m (m Int))
skolem2 = fmap unComp1 (skolem @(m :.: m))

skolem3 :: forall m. (PTraversable m) => Vec (m (m (m Int)))
skolem3 = fmap (fmap unComp1 . unComp1) (skolem @(m :.: m :.: m))

fIdx :: forall f a. (PTraversable f) => f a -> Int
fIdx = getIndex (coenum1 @f conquer)

eqDefault :: forall f a. (PTraversable f, Eq a) => f a -> f a -> Bool
eqDefault = coerce ((==) @(WrappedPTraversable f a))

cache :: Vec a -> Vec a
cache = Vec.fromVector . Vec.toVector

toVec :: Foldable t => t a -> Vec a
toVec = Vec.vec . toList
