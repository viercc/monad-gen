{-# LANGUAGE RankNTypes #-}
module ApplicativeLaws where

import Data.PTraversable

-- Monad properties

checkLeftUnit ::
  (PTraversable m, Eq x) =>
  (forall a. a -> m a) ->
  (forall a b c. (a -> b -> c) -> m a -> m b -> m c) ->
  m x ->
  Bool
checkLeftUnit pure' liftA2' mx = liftA2' ($) (pure' id) mx == mx

checkRightUnit ::
  (PTraversable m, Eq x) =>
  (forall a. a -> m a) ->
  (forall a b c. (a -> b -> c) -> m a -> m b -> m c) ->
  m x ->
  Bool
checkRightUnit pure' liftA2' mx = liftA2' const mx (pure' ()) == mx

checkAssoc ::
  (PTraversable m, Eq x, Eq y, Eq z) =>
  (forall a b c. (a -> b -> c) -> m a -> m b -> m c) ->
  m x -> m y -> m z ->
  Bool
checkAssoc liftA2' mx my mz = liftA2' ($) (liftA2' (,,) mx my) mz == liftA2' (\x (y,z) -> (x,y,z)) mx (liftA2' (,) my mz)
