{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.KeepLeft
-- Copyright   :  (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
module Data.Functor.KeepLeft where

import Data.Functor.Const (Const(..))
import Data.Semigroup (First(..))
import Data.Bitraversable (Bitraversable (..))
import Data.Bifoldable (Bifoldable)
import Data.Bifunctor (Bifunctor)

import Data.Functor.Classes ( Eq1, Ord1, Eq2, Ord2 )
import Data.Functor.Bind.Class ( Apply(..), Bind(..) )
import Control.Monad.Isolated ( Isolated(..) )
import Control.Monad.Ideal ( MonadIdeal(..), impureBindDefault )

import Data.Semigroup.Bifoldable (Bifoldable1)
import Data.Semigroup.Bitraversable (Bitraversable1)
import Data.Semigroup.Traversable.Class (Bitraversable1(..))

-- | Another choices of instances for 'Const'. @'KeepLeft' c@ have 'Apply' instance isomorphic to
--   @Const ('First' c)@, which can also (exceptionally) have 'Bind' instance.
--
-- The most used constant functor 'Const' lacks the instance of 'Bind', due to incompatibility
-- between 'Bind' and 'Apply'.
-- 
-- @
-- instance (Semigroup c) => 'Apply' ('Const' c)
-- @
-- 
-- While any @Semigroup c@ instance yields lawful @Apply (Const c)@ instance, large number of
-- them do not have @Bind@ instance compatible to @Apply@. One of few exceptional @Semigroup@
-- instance is ones isomorphic to @'First' c@ semigroup, whose semigroup operation is
-- "always use the left operand of @<>@."
--
-- @
-- (<>) :: c -> c -> c
-- x <> _ = x
-- @
newtype KeepLeft c a = KeepLeft { getKeepLeft :: c }
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Semigroup) via (First c)
  deriving (Eq1, Ord1, Apply) via (Const (First c))
  deriving (Eq2, Ord2, Bifunctor, Bifoldable, Bifoldable1) via Const

instance Bitraversable KeepLeft where
  bitraverse f _ (KeepLeft c) = KeepLeft <$> f c

instance Bitraversable1 KeepLeft where
  bitraverse1 f _ (KeepLeft c) = KeepLeft <$> f c

instance Bind (KeepLeft c) where
  KeepLeft c >>- _ = KeepLeft c

instance Isolated (KeepLeft c) where
  impureBind = impureBindDefault

-- | @Ideal (KeepLeft c) a ~ Either c a@
instance MonadIdeal (KeepLeft c) where
  idealBind (KeepLeft c) _ = KeepLeft c
