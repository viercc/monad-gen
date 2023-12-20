{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Data.PTraversable.Extra(
  skolem, skolem2, skolem3,
  shapes,

  _indices
) where

import           Control.Monad.State

import           GHC.Generics           ((:.:) (..))

import qualified Data.Vector as V

import           Data.PTraversable

type Fresh = State Int

fresh :: Fresh Int
fresh = state (\i -> (i, i+1))

runFresh :: Fresh a -> a
runFresh fa = evalState fa 0

var :: ([] :.: State Int) Int
var = Comp1 [fresh]

skolem :: forall m. (PTraversable m) => V.Vector (m Int)
skolem = V.fromList $ fmap runFresh . unComp1 $ enum1 var

skolem2 :: forall m. (PTraversable m) => V.Vector (m (m Int))
skolem2 = fmap unComp1 (skolem @(m :.: m))

skolem3 :: forall m. (PTraversable m) => V.Vector (m (m (m Int)))
skolem3 = fmap (fmap unComp1 . unComp1) (skolem @(m :.: m :.: m))

shapes :: forall f. (PTraversable f) => [f ()]
shapes = enum1 [()]

_indices :: Traversable t => t a -> t Int
_indices = runFresh . traverse (const fresh)
