{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Control.Monad.Isolate where

import Data.Foldable (toList)

import Data.Functor.Identity
import Data.Functor.Const
import Data.Void
import Data.Proxy
import Data.List.TwoOrMore
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NotOne

import Control.Monad.Ideal
import Data.Kind (Type)

-- | @MonadIsolate f m@ constrains a Monad @m@ to be isomorphic to
--   the sum of 'Data.Functor.Identity.Identity' and a Functor @f@.
--
-- In other words, @m@ must have a natural isomorphism 'isolatePure'.
--
-- @
-- isolatePure :: m a -> Either a (f a)
-- @
--
-- Additionaly, the inverse of the isomorphism must be @either pure injectImpure@.
--
-- @
-- 'either' 'pure' 'injectImpure' :: Either a (f a) -> m a
-- 
-- either pure injectImpure . isolatePure = id :: m a -> m a
-- isolatePure . either pure injectImpure = id :: Either a (f a) -> Either a (f a)
-- @
class (Monad m, Functor (Impurity m)) => MonadIsolate m where
  type Impurity m :: Type -> Type

  injectImpure :: Impurity m a -> m a
  isolatePure :: m a -> Either a (Impurity m a)

instance MonadIsolate (Either e) where
  type Impurity (Either e) = Const e
  injectImpure = Left . getConst
  isolatePure = either (Right . Const) Left

instance MonadIsolate Identity where
  type Impurity Identity = Const Void

  injectImpure = absurd . getConst
  isolatePure = Left . runIdentity

instance MonadIsolate Maybe where
  type Impurity Maybe = Proxy
  injectImpure _ = Nothing
  isolatePure = maybe (Right Proxy) Left

instance Semigroup s => MonadIsolate ((,) (Maybe s)) where
  type Impurity ((,) (Maybe s)) = (,) s

  injectImpure (s, a) = (Just s, a)
  isolatePure (Nothing, a) = Left a
  isolatePure (Just s, a)  = Right (s, a)

instance MonadIsolate NonEmpty where
  type Impurity NonEmpty = TwoOrMore

  isolatePure = twoOrMore
  injectImpure = toNonEmpty

instance MonadIsolate [] where
  type Impurity [] = NotOne

  isolatePure = notOne
  injectImpure = toList

-- | @'MonadIdeal' m@ implies @'MonadIsolate' m (Ideal m)@
instance MonadIdeal m => MonadIsolate (Ideal m) where
  type Impurity (Ideal m) = m
  
  isolatePure = runIdeal
  injectImpure = Ideal . Right