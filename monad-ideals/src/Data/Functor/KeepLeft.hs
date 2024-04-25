{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveTraversable #-}
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

newtype KeepLeft c a = KeepLeft { getKeepLeft :: c }
  deriving stock (Show, Read, Eq, Ord, Functor, Foldable, Traversable)
  deriving (Semigroup) via (First c)
  deriving (Eq1, Ord1) via (Const c)
  deriving (Eq2, Ord2, Bifunctor, Bifoldable, Bifoldable1) via Const

instance Bitraversable KeepLeft where
  bitraverse f _ (KeepLeft c) = KeepLeft <$> f c

instance Bitraversable1 KeepLeft where
  bitraverse1 f _ (KeepLeft c) = KeepLeft <$> f c

instance Apply (KeepLeft c) where
  KeepLeft c <.> _ = KeepLeft c

instance Bind (KeepLeft c) where
  KeepLeft c >>- _ = KeepLeft c

instance Isolated (KeepLeft c) where
  impureBind = impureBindDefault

-- | @Ideal (KeepLeft c) a ~ Either c a@
instance MonadIdeal (KeepLeft c) where
  idealBind (KeepLeft c) _ = KeepLeft c
