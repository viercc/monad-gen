{-# LANGUAGE RankNTypes #-}
module MonadLaws where

import Data.PTraversable

-- Monad properties

checkLeftUnit ::
  (PTraversable m, Eq b) =>
  (forall a. a -> m a) ->
  (forall a. m (m a) -> m a) ->
  m b ->
  Bool
checkLeftUnit pure' join' mb = join' (pure' mb) == mb

checkRightUnit ::
  (PTraversable m, Eq b) =>
  (forall a. a -> m a) ->
  (forall a. m (m a) -> m a) ->
  m b ->
  Bool
checkRightUnit pure' join' mb = join' (fmap pure' mb) == mb

checkAssoc ::
  (PTraversable m, Eq b) =>
  (forall a. m (m a) -> m a) ->
  m (m (m b)) ->
  Bool
checkAssoc join' mmmb = join' (join' mmmb) == join' (fmap join' mmmb)
