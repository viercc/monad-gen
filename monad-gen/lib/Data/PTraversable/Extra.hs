{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.PTraversable.Extra
  ( skolem,
    skolem2,
    skolem3,
    shapes
  )
where

import Data.PTraversable
import Data.Traversable.Extra
import qualified Data.Vector as V
import GHC.Generics ((:.:) (..))

var :: ([] :.: Fresh) Int
var = Comp1 [fresh]

skolem :: forall m. (PTraversable m) => V.Vector (m Int)
skolem = V.fromList $ fmap runFresh . unComp1 $ enum1 var

skolem2 :: forall m. (PTraversable m) => V.Vector (m (m Int))
skolem2 = fmap unComp1 (skolem @(m :.: m))

skolem3 :: forall m. (PTraversable m) => V.Vector (m (m (m Int)))
skolem3 = fmap (fmap unComp1 . unComp1) (skolem @(m :.: m :.: m))

shapes :: forall f. (PTraversable f) => [f ()]
shapes = enum1 [()]
