{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ConstraintKinds #-}
module Data.FunctorShape(
    Shape(Shape),
    mapShape,
    lengthShape, nullShape,

    Ignored(), ignoredValue, WeakEq, WeakOrd
) where

import qualified Unsafe.Coerce (unsafeCoerce)
import Data.Functor.Classes (showsUnaryWith)

import Data.PTraversable ( PTraversable(..) )
import Data.Finitary.Enum ( Enum(..) )
import Data.Profunctor.Cartesian ( Cartesian(proUnit) )
import Prelude hiding (Enum)
import Data.Profunctor.FinFn (withFinFn)

newtype Shape f = UnsafeMkShape { unsafeUnwrapShape :: f Ignored }
type role Shape representational

unsafeForget :: f a -> f Ignored
unsafeForget = Unsafe.Coerce.unsafeCoerce

type WeakEq f = Eq (f Ignored)

instance (WeakEq f) => Eq (Shape f) where
    UnsafeMkShape fa == UnsafeMkShape fb = fa == fb

type WeakOrd f = Ord (f Ignored)

instance (WeakOrd f) => Ord (Shape f) where
    UnsafeMkShape fa <= UnsafeMkShape fb = fa <= fb
    compare (UnsafeMkShape fa) (UnsafeMkShape fb) = compare fa fb

instance (Show (f Ignored)) => Show (Shape f) where
    showsPrec p (UnsafeMkShape fa) = showsUnaryWith showsPrec "Shape" p fa

instance PTraversable f => Enum (Shape f) where
    enumeration = ptraverseWith unsafeUnwrapShape Shape proUnit
    withEnum = withFinFn enumeration

instance Applicative f => Semigroup (Shape f) where
    UnsafeMkShape fa <> UnsafeMkShape fb = UnsafeMkShape (fa *> fb)

instance Applicative f => Monoid (Shape f) where
    mempty = UnsafeMkShape (pure ignoredValue)

{-# COMPLETE Shape #-}
pattern Shape :: f a -> Shape f
pattern Shape x <- UnsafeMkShape x
  where Shape x = UnsafeMkShape (unsafeForget x)

mapShape :: (forall a. f a -> g a) -> Shape f -> Shape g
mapShape fg (Shape f) = Shape (fg f)

lengthShape :: Foldable f => Shape f -> Int
lengthShape = length . unsafeUnwrapShape

nullShape :: Foldable f => Shape f -> Bool
nullShape = null . unsafeUnwrapShape

-- * Type for ignored values

data Ignored = Ignored

ignoredValue :: Ignored
ignoredValue = Ignored

instance Eq Ignored where
    _ == _ = True

instance Ord Ignored where
    _ <= _ = True
    compare _ _ = EQ

instance Show Ignored where
    show _ = "_"
