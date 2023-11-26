{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.FunctorShape(
    Shape(), pattern Shape,
    Boring(..), WeakEq, WeakOrd
) where

import qualified Unsafe.Coerce (unsafeCoerce)
import Data.Functor.Classes (showsUnaryWith)

newtype Shape f = UnsafeMkShape (f Boring)
type role Shape representational

type WeakEq f = Eq (f Boring)

instance (WeakEq f) => Eq (Shape f) where
    UnsafeMkShape fa == UnsafeMkShape fb = fa == fb

type WeakOrd f = Ord (f Boring)

instance (WeakOrd f) => Ord (Shape f) where
    UnsafeMkShape fa <= UnsafeMkShape fb = fa <= fb
    compare (UnsafeMkShape fa) (UnsafeMkShape fb) = compare fa fb

instance (Show (f Boring)) => Show (Shape f) where
    showsPrec p (UnsafeMkShape fa) = showsUnaryWith showsPrec "Shape" p fa

{-# COMPLETE Shape #-}
pattern Shape :: f a -> Shape f
pattern Shape x <- UnsafeMkShape x
  where Shape x = UnsafeMkShape (forget x)

data Boring = Boring

forget :: f a -> f Boring
forget = Unsafe.Coerce.unsafeCoerce

instance Eq Boring where
    _ == _ = True

instance Ord Boring where
    _ <= _ = True
    compare _ _ = EQ

instance Show Boring where
    show _ = "_"
