module LensUtil where

import Data.Functor.Const
import Data.Monoid (Endo (..))

type LensLike f s t a b = (a -> f b) -> s -> f t

foldMapOf :: LensLike (Const m) s t a b -> (a -> m) -> s -> m
foldMapOf trav f = getConst . trav (Const . f)

toListOf :: LensLike (Const (Endo [a])) s t a b -> s -> [a]
toListOf trav = concretize . foldMapOf trav (\a -> Endo (a:))
  where
    concretize endo = appEndo endo []
