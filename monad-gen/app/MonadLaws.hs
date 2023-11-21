{-# LANGUAGE RankNTypes #-}
module MonadLaws where

import Data.PTraversable
import Data.PTraversable.Extra (eqDefault)

-- Monad properties

checkLeftUnit ::
  (PTraversable m, Eq b) =>
  (forall a. a -> m a) ->
  (forall a. m (m a) -> m a) ->
  m b ->
  Bool
checkLeftUnit pure' join' mb = join' (pure' mb) `eqDefault` mb

checkRightUnit ::
  (PTraversable m, Eq b) =>
  (forall a. a -> m a) ->
  (forall a. m (m a) -> m a) ->
  m b ->
  Bool
checkRightUnit pure' join' mb = join' (fmap pure' mb) `eqDefault` mb

checkAssoc ::
  (PTraversable m, Eq b) =>
  (forall a. m (m a) -> m a) ->
  m (m (m b)) ->
  Bool
checkAssoc join' mmmb = join' (join' mmmb) `eqDefault` join' (fmap join' mmmb)
