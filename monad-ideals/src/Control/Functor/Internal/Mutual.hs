{-# LANGUAGE TypeOperators #-}
module Control.Functor.Internal.Mutual where

import Data.Bifunctor

newtype Mutual p m n a = Mutual {runMutual :: m (p a (Mutual p n m a))}

newtype Mutual' p m n a = Mutual' {runMutual' :: p (Mutual p m n a) (Mutual p n m a)}

instance (Bifunctor p, Functor m, Functor n) => Functor (Mutual p m n) where
  fmap f = Mutual . fmap (bimap f (fmap f)) . runMutual

instance (Bifunctor p, Functor m, Functor n) => Functor (Mutual' p m n) where
  fmap f = Mutual' . bimap (fmap f) (fmap f) . runMutual'

type m :+ n = Mutual' Either m n

inject1 :: (Functor m) => m a -> (m :+ n) a
inject1 = Mutual' . Left . Mutual . fmap Left

inject2 :: (Functor n) => n a -> (m :+ n) a
inject2 = Mutual' . Right . Mutual . fmap Left

type w :* v = Mutual' (,) w v

project1 :: (Functor w) => (w :* v) a -> w a
project1 = fmap fst . runMutual . fst . runMutual'

project2 :: (Functor v) => (w :* v) a -> v a
project2 = fmap fst . runMutual . snd . runMutual'
