{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Isolated
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Monad.Isolated(
  -- * Impure part isolated from a Monad
  Isolated(..),

  -- * (Re)Unite a Monad from pure and impure parts
  Unite(..),
  hoistUnite,
) where

import Data.Functor.Bind
import Data.Semigroup.Traversable
import Data.Semigroup.Foldable
import Data.Bifunctor (Bifunctor(..))
import Data.Proxy
import Control.Applicative (WrappedMonad(..))

newtype Unite f a = Unite { runUnite :: Either a (f a) }
  deriving (Show, Read, Eq, Ord)

hoistUnite :: (forall a. f a -> g a) -> Unite f b -> Unite g b
hoistUnite fg = Unite . fmap fg . runUnite

instance (Functor g) => Functor (Unite g) where
  fmap f = Unite . bimap f (fmap f) . runUnite

instance (Foldable g) => Foldable (Unite g) where
  foldMap f = either f (foldMap f) . runUnite

instance (Foldable1 g) => Foldable1 (Unite g) where
  foldMap1 f = either f (foldMap1 f) . runUnite

instance (Traversable g) => Traversable (Unite g) where
  traverse f = fmap Unite . either (fmap Left . f) (fmap Right . traverse f) . runUnite

instance (Traversable1 g) => Traversable1 (Unite g) where
  traverse1 f = fmap Unite . either (fmap Left . f) (fmap Right . traverse1 f) . runUnite

-- | @Isolated m0@ is a @Functor@ which can be thought of as an impure part of a @Monad@.
-- 
-- ==== Examples
-- 
-- - 'Proxy' is @Isolated@ by being same to the 'Nothing' part of the 'Maybe' monad.
--
-- - 'Data.List.NotOne.NotOne' is @Isolated@ by being the list monad ('[]') minus singleton lists,
--   the 'pure' part of the list monad.
--
-- ==== Non-example
--
-- Not every @Monad@ can be isolated its pure and impure parts as the sum of functors.
-- For example, the reader monad cannot be written as a sum of two functors.
--
-- ==== Laws
-- 
-- 'impureBind' must be implemented so that the @Monad (Unite m0)@ instance derived from
-- it is lawful.
-- 
-- @
-- return a = Unite (Left a)
-- 
-- Unite (Left a) >>= k = k a
-- Unite (Right ma) >>= k = ma \`impureBind\` k
-- @
-- 
-- Translating the @Monad@ laws on @Unite m0@ in terms of @impureBind@,
-- the following equations are the @Isolated@ laws on its own.
--
-- - (Right identity)
--
--     @
--     ma \`impureBind\` Unite . Left === Unite (Right ma)
--     @
--
-- - (Associativity)
--
--     @
--     (ma \`impureBind\` f) \`impureBind\` g === ma `impureBind` \a -> either g (\`impureBind\` g) (runUnite fa)
--     @
class Functor m0 => Isolated m0 where
  impureBind :: m0 a -> (a -> Unite m0 b) -> Unite m0 b

infixl 1 `impureBind`

instance Isolated m0 => Apply (Unite m0) where
  (<.>) = apDefault

instance Isolated m0 => Applicative (Unite m0) where
  pure = Unite . Left
  (<*>) = (<.>)

instance Isolated m0 => Bind (Unite m0) where
  Unite (Left a) >>- k = k a
  Unite (Right ma) >>- k = ma `impureBind` k

instance Isolated m0 => Monad (Unite m0) where
  (>>=) = (>>-)

instance Isolated Proxy where
  _ `impureBind` _ = Unite (Right Proxy)

instance Semigroup s => Isolated ((,) s) where
  (s, a) `impureBind` k = case runUnite (k a) of
    Left b -> Unite (Right (s, b))
    Right (s', b) -> Unite (Right (s <> s', b))

instance Monad m => Isolated (WrappedMonad m) where
  WrapMonad ma `impureBind` k = Unite . Right . WrapMonad $ ma >>= \a ->
    case runUnite (k a) of
      Left b -> pure b
      Right (WrapMonad mb) -> mb
