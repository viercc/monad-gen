{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module GHC.Generics.Orphans where

import GHC.Generics ( Generic1(..), Generically1(..) )

instance (Generic1 t, Foldable (Rep1 t)) => Foldable (Generically1 t) where
  foldMap f (Generically1 ta) = foldMap f (from1 ta)

instance (Generic1 t, Traversable (Rep1 t)) => Traversable (Generically1 t) where
  traverse f (Generically1 ta) = Generically1 . to1 <$> traverse f (from1 ta)