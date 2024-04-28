
{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Ideal
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Monad.Ideal
  ( -- * Ideal Monads
    MonadIdeal (..), idealize,

    Ideal, ideal, runIdeal, hoistIdeal,

    destroyIdeal,

    bindDefault,
    impureBindDefault,
    
    -- * Relation between @MonadIdeal@, @Bind@, and @Isolated@
    -- 
    -- $relation_to_bind_and_isolate
  )
where

import Prelude
import Control.Arrow ((|||))

import Data.Functor.Bind (Bind (..))
import Control.Applicative (WrappedMonad (..))

import Control.Monad.Isolated

-- | Ideal monad is a special case of @Unite m0@
type Ideal = Unite

-- | Constructor of @Ideal@, for backward compatibility
ideal :: Either a (m0 a) -> Ideal m0 a
ideal = Unite

-- | Deconstructor of @Ideal@, for backward compatibility
runIdeal :: Ideal m0 a -> Either a (m0 a)
runIdeal = runUnite

-- | Alias of 'hoistUnite' for naming consistently
hoistIdeal :: (forall a. m0 a -> n a) -> Ideal m0 b -> Ideal n b
hoistIdeal = hoistUnite

-- | @m0@ is the "ideal part" of an ideal monad.
--
-- ==== Laws
--
-- Methods inherited from superclasses must be equivalent to the
-- canocical ones.
--
-- - @'(>>-)' === 'bindDefault'@
-- - @'impureBind' === 'impureBindDefault'@
class (Bind m0, Isolated m0) => MonadIdeal m0 where
  idealBind :: m0 a -> (a -> Ideal m0 b) -> m0 b

infixl 1 `idealBind`

idealize :: (MonadIdeal m0) => m0 (Ideal m0 a) -> m0 a
idealize = (`idealBind` id)

-- | 'MonadIdeal' implies 'Bind'
bindDefault :: MonadIdeal m0 => m0 a -> (a -> m0 b) -> m0 b
bindDefault ma k = ma `idealBind` ideal . Right . k

-- | 'MonadIdeal' implies 'Isolated'
impureBindDefault :: MonadIdeal m0 => m0 a -> (a -> Unite m0 b) -> Unite m0 b
impureBindDefault ma k = ideal . Right $ ma `idealBind` k

-- | @Ideal ((,) s) ~ (,) (Maybe s)@
instance (Semigroup s) => MonadIdeal ((,) s) where
  idealBind (s1, a) k = case runIdeal (k a) of
    Left b -> (s1, b)
    Right (s2, b) -> (s1 <> s2, b)

-- | Any @Monad m@ can be an ideal of @Ideal m@
instance (Monad m) => MonadIdeal (WrappedMonad m) where
  idealBind (WrapMonad ma) k = WrapMonad $ ma >>= either pure unwrapMonad . runIdeal . k

destroyIdeal :: (m0 a -> a) -> Ideal m0 a -> a
destroyIdeal phi = (id ||| phi) . runIdeal

{- $relation_to_bind_and_isolate

@MonadIdeal@ is a requirement stronger than both of 'Bind' and 'Isolated'.
In fact, these subset relations hold.

- Every @MonadIdeal@ is @Bind@
- Every @MonadIdeal@ is @Isolated@

These are /strict/ subset relation and neither of three classes can be dropped.

- 'Data.List.NotOne.NotOne' is both @Bind@ and @Isolated@, but not @MonadIdeal@.

- @NullBind c@ is @Bind@ but can't be @Isolated@, because @Unite (NullBind c)@ can't be a @Monad@ in a compatible way.

    @
    newtype NullBind c a = NullBind (Maybe c)
    instance Bind (NullBind c a) where
      _ >>- _ = NullBind Nothing
    @

- @Toggle@ shown below is @Isolated@, but can't be a @Bind@ in a compatible way.

    @
    newtype Toggle a = Toggle a
      deriving Functor

    instance Isolated Toggle where
      impureBind (Toggle a) k = case k a of
        Unite (Left b)           -> Unite (Right (Toggle b))
        Unite (Right (Toggle b)) -> Unite (Left b)
    @

-}
