{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
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
class (Monad m, Functor f) => MonadIsolate f m | m -> f where
  injectImpure :: f a -> m a
  isolatePure :: m a -> Either a (f a)

instance MonadIsolate (Const e) (Either e) where
  injectImpure = Left . getConst
  isolatePure = either (Right . Const) Left

instance MonadIsolate (Const Void) Identity where
  injectImpure = absurd . getConst
  isolatePure = Left . runIdentity

instance MonadIsolate Proxy Maybe where
  injectImpure _ = Nothing
  isolatePure = maybe (Right Proxy) Left

instance Semigroup s => MonadIsolate ((,) s) ((,) (Maybe s)) where
  injectImpure (s, a) = (Just s, a)
  isolatePure (Nothing, a) = Left a
  isolatePure (Just s, a)  = Right (s, a)

instance MonadIsolate TwoOrMore NonEmpty where
  isolatePure = twoOrMore
  injectImpure = toNonEmpty

instance MonadIsolate NotOne [] where
  isolatePure = notOne
  injectImpure = toList

-- | @'MonadIdeal' m@ implies @'MonadIsolate' m (Ideal m)@
instance MonadIdeal m => MonadIsolate m (Ideal m) where
  isolatePure = runIdeal
  injectImpure = Ideal . Right