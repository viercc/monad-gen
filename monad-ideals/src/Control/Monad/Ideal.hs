
{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.ideal
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

-- | Ideal monad is a special case of @Unite m@
type Ideal = Unite

-- | Constructor of @ideal@ = @Unite@ for backward compatibility
ideal :: Either a (m a) -> Ideal m a
ideal = Unite

-- | Deconstructor of @ideal@ = @Unite@ for backward compatibility
runIdeal :: Ideal m a -> Either a (m a)
runIdeal = runUnite

-- | Alias of 'hoistUnite' for naming consistently
hoistIdeal :: (forall a. m a -> n a) -> Ideal m b -> Ideal n b
hoistIdeal = hoistUnite

-- | @m@ is the "ideal part" of an ideal monad.
--
-- ==== Laws
--
-- Methods inherited from superclasses must be equivalent to the
-- canocical ones.
--
-- - @'(>>-)' === 'bindDefault'@
-- - @'impureBind' === 'impureBindDefault'@
class (Bind m, Isolated m) => MonadIdeal m where
  idealBind :: m a -> (a -> Ideal m b) -> m b

infixl 1 `idealBind`

idealize :: (MonadIdeal m) => m (Ideal m a) -> m a
idealize = (`idealBind` id)

-- | 'MonadIdeal' implies 'Bind'
bindDefault :: MonadIdeal m => m a -> (a -> m b) -> m b
bindDefault ma k = ma `idealBind` ideal . Right . k

-- | 'MonadIdeal' implies 'Isolated'
impureBindDefault :: MonadIdeal m => m a -> (a -> Unite m b) -> Unite m b
impureBindDefault ma k = ideal . Right $ ma `idealBind` k

-- | @ideal ((,) s) ~ (,) (Maybe s)@
instance (Semigroup s) => MonadIdeal ((,) s) where
  idealBind (s1, a) k = case runIdeal (k a) of
    Left b -> (s1, b)
    Right (s2, b) -> (s1 <> s2, b)

-- | Any @Monad@ can be an ideal of @ideal m@
instance (Monad m) => MonadIdeal (WrappedMonad m) where
  idealBind (WrapMonad ma) k = WrapMonad $ ma >>= either pure unwrapMonad . runIdeal . k

destroyIdeal :: (m a -> a) -> Ideal m a -> a
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
