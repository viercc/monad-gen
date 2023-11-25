{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module GHC.Generics.Orphans where

import GHC.Generics

deriving newtype instance Foldable t => Foldable (Generically1 t)
instance (Generic1 t, Functor (Rep1 t), Traversable t) => Traversable (Generically1 t) where
    traverse f (Generically1 ta) = Generically1 <$> traverse f ta