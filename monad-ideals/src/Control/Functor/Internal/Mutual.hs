{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Functor.Internal.Mutual
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Functor.Internal.Mutual where

import Data.Bifunctor

newtype Mutual p m n a = Mutual {runMutual :: m (p a (Mutual p n m a))}

instance (Bifunctor p, Functor m, Functor n) => Functor (Mutual p m n) where
  fmap f = Mutual . fmap (bimap f (fmap f)) . runMutual

foldMutual
  :: Bifunctor p
  => (forall a b. t a -> (a -> p b (t b)) -> t b)
  -> (forall a. m a -> t a)
  -> (forall a. n a -> t a)
  -> Mutual p m n c -> t c
foldMutual bind mt nt = (`bind` second (foldMutual bind nt mt)) . mt . runMutual

unfoldMutual
  :: Bifunctor p
  => (forall a b. (p a (s a) -> b) -> s a -> s b)
  -> (forall a. s a -> w a)
  -> (forall a. s a -> v a)
  -> s c -> Mutual p w v c
unfoldMutual ext sw sv = Mutual . sw . ext (second (unfoldMutual ext sv sw))
