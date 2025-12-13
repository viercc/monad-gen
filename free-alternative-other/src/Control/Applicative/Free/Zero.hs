{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}

-- | An applicative with left zero @f@ is an 'Applicative'
-- with polymorphic zero action which stops
-- all actions right to zero.
--
-- @
-- -- Type of zero action
-- zero :: forall a. f a
-- 
-- -- Left zero law
-- zero \<*\> x === zero
-- @
-- 
-- This module provides the free construction of them
-- in a way similar to the free monad or the free applicative.
module Control.Applicative.Free.Zero where

import Control.Applicative (Alternative(..), (<**>))

-- | Free (applicative with left zero).
data Free f a where
  Pure :: a -> Free f a
  Zero :: Free f a
  Ap :: f a -> Free f (a -> b) -> Free f b

instance Functor (Free f) where
  fmap f (Pure r) = Pure (f r)
  fmap _ Zero = Zero
  fmap f (Ap fa mk) = Ap fa ((f .) <$> mk)

instance Applicative (Free f) where
  pure = Pure

  liftA2 op (Pure x) y = op x <$> y
  liftA2 _ Zero _ = Zero
  liftA2 op (Ap fa mk) y = Ap fa (liftA2 (\g b a -> op (g a) b) mk y)

-- | /Left zero/ + /Left catch/
instance Alternative (Free f) where
  empty = Zero
  (<|>) = trap

hoistFree :: (forall x. f x -> g x) -> Free f a -> Free g a
hoistFree _ (Pure a) = Pure a
hoistFree _ Zero = Zero
hoistFree fg (Ap fa mk) = Ap (fg fa) (hoistFree fg mk)


-- | Recovery from 'Zero'.
--
-- @'trap' x y@ first look at @x@ if it ends with @Zero@ constructor.
-- If @x@ ends with @Pure@, return @x@ itself.
-- Otherwise, it replaces @Zero@ in x with @y@.
--
-- @
-- 'trap' (Ap f1 (Ap f2 ... Zero)) y === Ap f1 (Ap f2 ... y)
-- @
trap :: Free f a -> Free f a -> Free f a
trap = go id
  where
    go :: (b -> a) -> Free f a -> Free f b -> Free f a
    go _ (Pure a) _ = Pure a
    go p Zero y = p <$> y
    go p (Ap fa mk) y = Ap fa (go (const . p) mk y)

-- * Interpreting

interpret :: Applicative f => (forall r. f r) -> Free f a -> f a
interpret _ (Pure a) = pure a
interpret z Zero = z
interpret z (Ap fa mk) = fa <**> interpret z mk

interpretAlternative :: Alternative f => Free f a -> f a
interpretAlternative = interpret empty

interpretMaybeT :: Monad f => Free f a -> f (Maybe a)
interpretMaybeT (Pure a) = pure (Just a)
interpretMaybeT Zero = pure Nothing
interpretMaybeT (Ap fa mk) = fa >>= \a -> fmap ($ a) <$> interpretMaybeT mk 
