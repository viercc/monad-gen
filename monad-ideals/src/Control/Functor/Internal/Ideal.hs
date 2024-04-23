{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
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

  , TwoOrMore(..)
  , WrapMonad(..)

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
  , inject1
  , inject2
  , (||||)
  ) where

import Prelude

import Control.Monad (ap)
import Data.Bifunctor
import Control.Comonad
import Control.Arrow ((|||), (&&&))
import Data.Functor.Const
import Data.Foldable (toList)

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

-- | @Ideal (Const c) a ~ Either c a@
instance MonadIdeal (Const c) where
  idealBind (Const c) _ = Const c

-- | @Ideal ((,) s) ~ (,) (Maybe s)@
instance Semigroup s => MonadIdeal ((,) s) where
  idealBind (s1, a) k = case runIdeal (k a) of
    Left b -> (s1, b)
    Right (s2, b) -> (s1 <> s2, b)

data TwoOrMore a = TwoOrMore a a [a]
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

idealToList :: Ideal TwoOrMore a -> [a]
idealToList = either (: []) toList . runIdeal

-- | @Ideal TwoOrMore ~ NonEmpty@
instance MonadIdeal TwoOrMore where
  idealBind (TwoOrMore a1 a2 as) k = case (runIdeal (k a1), runIdeal (k a2)) of
    (Left b1, Left b2) -> TwoOrMore b1 b2 (as >>= idealToList . k)
    (Left b1, Right (TwoOrMore b2 b3 bs)) -> TwoOrMore b1 b2 (b3 : bs ++ (as >>= idealToList . k))
    (Right (TwoOrMore b1 b2 bs), rest) -> TwoOrMore b1 b2 (bs ++ either (: []) toList rest ++ (as >>= idealToList . k))

-- | Any 'Monad' can be seen as a 'MonadIdeal'
newtype WrapMonad m a = WrapMonad { unwrapMonad :: m a }
  deriving (Show, Read, Eq, Ord, Functor)

instance Monad m => MonadIdeal (WrapMonad m) where
  idealBind (WrapMonad ma) k = WrapMonad $ ma >>= either pure unwrapMonad . runIdeal . k

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

inject1 :: MonadIdeal m => m a -> (m :+ n) a
inject1 ma = Mutual' $ Left $ Mutual $ Left <$> ma

inject2 :: MonadIdeal n => n a -> (m :+ n) a
inject2 na = Mutual' $ Right $ Mutual $ Left <$> na

(||||) :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> (m :+ n) b -> t b
mt |||| nt = either (foldMutual mt nt) (foldMutual nt mt). runMutual'

foldMutual :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> Mutual Either m n b -> t b
foldMutual mt nt (Mutual mn) = mt mn `idealBind` (ideal . fmap (foldMutual nt mt))

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