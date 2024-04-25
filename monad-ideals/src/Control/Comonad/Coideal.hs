{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveTraversable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Coideal
-- Copyright   :  (C) 2008 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Comonad.Coideal
  ( -- * Coideal Comonads
    ComonadCoideal (..),
    Coideal(..),
    buildCoideal,

    -- * Mutual recursion for (co)ideal (co)monad (co)products
    Mutual (..),

    -- * Coideal Comonad Product
    (:*)(..),
    project1, project2,
    (&&&&)
  )
where

import Control.Arrow ((&&&))
import Control.Comonad

import Control.Functor.Internal.Mutual
import Data.Bifunctor (Bifunctor(..))

newtype Coideal f a = Coideal { runCoideal :: (a, f a) }
  deriving (Functor, Foldable, Traversable)

class (Functor w) => ComonadCoideal w where
  coidealExtend :: (Coideal w a -> b) -> w a -> w b

coidealize :: (ComonadCoideal w) => w a -> w (Coideal w a)
coidealize = coidealExtend id

instance (ComonadCoideal w) => Comonad (Coideal w) where
  extract = fst . runCoideal
  extend f = fmap f . Coideal . (id &&& coidealize . snd . runCoideal)

buildCoideal :: (a -> w a) -> a -> Coideal w a
buildCoideal phi = Coideal . (id &&& phi)

-- * (Co)ideal (Co)products

newtype (:*) w v a = CoidealProduct { runCoidealProduct :: (Mutual (,) w v a, Mutual (,) v w a) }
  deriving Functor

project1 :: (Functor w) => (w :* v) a -> w a
project1 = fmap fst . runMutual . fst . runCoidealProduct

project2 :: (Functor v) => (w :* v) a -> v a
project2 = fmap fst . runMutual . snd . runCoidealProduct

instance (ComonadCoideal w, ComonadCoideal v) => ComonadCoideal (w :* v) where
  coidealExtend k (CoidealProduct (wv, vw)) = CoidealProduct (extendMutual1 k wv, extendMutual2 k vw)

extendMutual1 ::
  (ComonadCoideal w, ComonadCoideal v) =>
  (Coideal (w :* v) a -> b) ->
  Mutual (,) w v a ->
  Mutual (,) w v b
extendMutual1 k (Mutual wv) =
  Mutual $ coidealExtend (\(Coideal ((a, vw), w')) -> (k (Coideal (a, CoidealProduct (Mutual w', vw))), extendMutual2 k vw)) wv

extendMutual2 ::
  (ComonadCoideal w, ComonadCoideal v) =>
  (Coideal (v :* w) a -> b) ->
  Mutual (,) w v a ->
  Mutual (,) w v b
extendMutual2 k (Mutual wv) =
  Mutual $ coidealExtend (\(Coideal ((a, vw), w')) -> (k (Coideal (a, CoidealProduct (vw, Mutual w'))), extendMutual1 k vw)) wv

(&&&&) :: (ComonadCoideal t) => (forall a. t a -> w a) -> (forall a. t a -> v a) -> t b -> (w :* v) b
tw &&&& tv = CoidealProduct . (unfoldMutual tw tv &&& unfoldMutual tv tw)

unfoldMutual :: (ComonadCoideal t) => (forall a. t a -> w a) -> (forall a. t a -> v a) -> t b -> Mutual (,) w v b
unfoldMutual tw tv t = Mutual $ tw $ coidealExtend (second (unfoldMutual tv tw) . runCoideal) t
