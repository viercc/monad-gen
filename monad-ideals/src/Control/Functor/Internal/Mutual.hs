module Control.Functor.Internal.Mutual where

import Data.Bifunctor

newtype Mutual p m n a = Mutual {runMutual :: m (p a (Mutual p n m a))}

instance (Bifunctor p, Functor m, Functor n) => Functor (Mutual p m n) where
  fmap f = Mutual . fmap (bimap f (fmap f)) . runMutual
