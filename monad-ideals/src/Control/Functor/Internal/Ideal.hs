{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Functor.Internal.Ideal
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
----------------------------------------------------------------------------
module Control.Functor.Internal.Ideal
  (
  -- * Common shape of (co)ideal
    Ap(..)

  -- * Ideal Monads
  , MonadIdeal(..)
  , Ideal
  , ideal
  , destroyIdeal
  -- * Coideal Comonads
  , ComonadCoideal(..)
  , Coideal
  , coideal
  , buildCoideal
  -- * Mutual recursion for (co)ideal (co)monad (co)products
  , Mutual(..)
  , Mutual'(..)
  -- * Coideal Comonad Product
  , (:*)
  -- * Ideal Monad Coproduct
  , (:+)
  ) where

import Prelude

import Control.Monad (ap)
import Data.Bifunctor
import Control.Comonad
import Control.Arrow ((|||), (&&&))

newtype Ap t f a = MkAp { runAp :: t a (f a) }

instance (Bifunctor t, Functor g) => Functor (Ap t g) where
  fmap f = MkAp . bimap f (fmap f) . runAp

type Ideal = Ap Either
type Coideal = Ap (,)

ideal :: Either a (f a) -> Ideal f a
ideal = MkAp

coideal :: (a, f a) -> Coideal f a
coideal = MkAp

runIdeal :: Ideal f a -> Either a (f a)
runIdeal = runAp

runCoideal :: Coideal f a -> (a, f a)
runCoideal = runAp

class Functor m => MonadIdeal m where
  idealBind :: m a -> (a -> Ideal m b) -> m b

idealize :: MonadIdeal m => m (Ideal m a) -> m a
idealize = (`idealBind` id)

instance MonadIdeal m => Applicative (Ideal m) where
  pure = ideal . Left
  (<*>) = ap

instance MonadIdeal m => Monad (Ideal m) where
  m >>= f = (id ||| ideal . Right . idealize) . runIdeal $ fmap f m

destroyIdeal :: (m a -> a) -> Ideal m a -> a
destroyIdeal phi = (id ||| phi) . runIdeal


class Functor w => ComonadCoideal w where
  coidealExtend :: (Coideal w a -> b) -> w a -> w b

coidealize :: ComonadCoideal w => w a -> w (Coideal w a)
coidealize = coidealExtend id

instance ComonadCoideal w => Comonad (Coideal w) where
  extract = fst . runCoideal
  extend f = fmap f . coideal . (id &&& coidealize . snd . runCoideal)

buildCoideal :: (a -> w a) -> a -> Coideal w a
buildCoideal phi = coideal . (id &&& phi)

-- instance ComonadCoideal (Fst k) where
-- coidealize = mkFst . runFst

-- * (Co)ideal (Co)products

newtype Mutual p m n a = Mutual { runMutual :: m (p a (Mutual p n m a)) }
newtype Mutual' p m n a = Mutual' { runMutual' :: p (Mutual p m n a) (Mutual p n m a) }
type (m :+ n) = Mutual' Either m n
type (m :* n) = Mutual' (,) m n

instance (Bifunctor p, Functor m, Functor n) => Functor (Mutual p m n) where
  fmap f = Mutual . fmap (bimap f (fmap f)) . runMutual

instance (Bifunctor p, Functor m, Functor n) => Functor (Mutual' p m n) where
  fmap f = Mutual' . bimap (fmap f) (fmap f) . runMutual'

instance (MonadIdeal m, MonadIdeal n) => MonadIdeal (m :+ n) where
  idealBind mutual k = Mutual' $ case runMutual' mutual of
    Left mn -> Left $ bindMutual1 mn k
    Right nm -> Right $ bindMutual2 nm k

bindMutual1 :: (MonadIdeal m, MonadIdeal n) => Mutual Either m n a -> (a -> Ideal (Mutual' Either m n) b) -> Mutual Either m n b
bindMutual1 (Mutual mn) k = Mutual $ mn `idealBind` \next ->
  case next of
    Left a -> case runIdeal (k a) of
      Left b -> pure (Left b)
      Right (Mutual' (Left mn')) -> ideal . Right $ runMutual mn'
      Right (Mutual' (Right nm')) -> pure (Right nm')
    Right nm -> pure . Right $ bindMutual2 nm k

bindMutual2 :: (MonadIdeal m, MonadIdeal n) => Mutual Either m n a -> (a -> Ideal (Mutual' Either n m) b) -> Mutual Either m n b
bindMutual2 (Mutual mn) k = Mutual $ mn `idealBind` \next ->
  case next of
    Left a -> case runIdeal (k a) of
      Left b -> pure (Left b)
      Right (Mutual' (Left nm')) -> pure (Right nm')
      Right (Mutual' (Right mn')) -> ideal . Right $ runMutual mn'
    Right nm -> pure . Right $ bindMutual1 nm k

instance (ComonadCoideal w, ComonadCoideal v) => ComonadCoideal (w :* v) where
  coidealExtend k (Mutual' (wv, vw)) = Mutual' (extendMutual1 k wv, extendMutual2 k vw)

extendMutual1 :: (ComonadCoideal w, ComonadCoideal v)
  => (Coideal (Mutual' (,) w v) a -> b) -> Mutual (,) w v a -> Mutual (,) w v b
extendMutual1 k (Mutual wv) =
  Mutual $ coidealExtend (\ (MkAp ((a, vw), w')) -> (k (coideal (a, Mutual' (Mutual w', vw))), extendMutual2 k vw)) wv

extendMutual2 :: (ComonadCoideal w, ComonadCoideal v)
  => (Coideal (Mutual' (,) v w) a -> b) -> Mutual (,) w v a -> Mutual (,) w v b
extendMutual2 k (Mutual wv) =
  Mutual $ coidealExtend (\ (MkAp ((a, vw), w')) -> (k (coideal (a, Mutual' (vw, Mutual w'))), extendMutual1 k vw)) wv