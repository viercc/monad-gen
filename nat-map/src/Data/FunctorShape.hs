{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.FunctorShape(
    Shape(), pattern Shape,
    mapShape,
    Ignored(..), WeakEq, WeakOrd
) where

import qualified Unsafe.Coerce (unsafeCoerce)
import Data.Functor.Classes (showsUnaryWith)

newtype Shape f = UnsafeMkShape (f Ignored)
type role Shape representational

type WeakEq f = Eq (f Ignored)

instance (WeakEq f) => Eq (Shape f) where
    UnsafeMkShape fa == UnsafeMkShape fb = fa == fb

type WeakOrd f = Ord (f Ignored)

instance (WeakOrd f) => Ord (Shape f) where
    UnsafeMkShape fa <= UnsafeMkShape fb = fa <= fb
    compare (UnsafeMkShape fa) (UnsafeMkShape fb) = compare fa fb

instance (Show (f Ignored)) => Show (Shape f) where
    showsPrec p (UnsafeMkShape fa) = showsUnaryWith showsPrec "Shape" p fa

{-# COMPLETE Shape #-}
pattern Shape :: f a -> Shape f
pattern Shape x <- UnsafeMkShape x
  where Shape x = UnsafeMkShape (forget x)

mapShape :: (forall a. f a -> g a) -> Shape f -> Shape g
mapShape fg (Shape f) = Shape (fg f)

data Ignored = Ignored

forget :: f a -> f Ignored
forget = Unsafe.Coerce.unsafeCoerce

instance Eq Ignored where
    _ == _ = True

instance Ord Ignored where
    _ <= _ = True
    compare _ _ = EQ

instance Show Ignored where
    show _ = "_"
