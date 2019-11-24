{-# LANGUAGE ScopedTypeVariables, TypeOperators, TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
module Enum1.Extra(
  skolem, skolem2, skolem3,
  
  allPures,

  Template(),
  enumTemplates,
  runTemplate
) where

import Data.Kind

import Control.Monad.State

import GHC.Generics

import Data.Functor.Numbering
import Util
import Enum1

skolem :: forall m. (Traversable m, Enum1 m) => FromN (m Int)
skolem = fmap fillIn $ enum1 $ vec [state (\i -> (i, i+1))]
  where fillIn mx = evalState (sequenceA mx) 0

skolem2 :: forall m. (Traversable m, Enum1 m) => FromN (m (m Int))
skolem2 = fmap unComp1 (skolem @(m :.: m))

skolem3 :: forall m. (Traversable m, Enum1 m) => FromN (m (m (m Int)))
skolem3 = fmap (fmap unComp1 . unComp1) (skolem @(m :.: m :.: m))

-----------------------------------

newtype Template (f :: Type -> Type) g = MkTemplate (FromN (Int, g ()))

enumTemplates
  :: forall f g.
     (Enum1 f, Foldable f, Enum1 g)
  => FromN (Template f g)
enumTemplates = coerceMap MkTemplate (traverse entry fs)
  where
    fs = enum1 @f (singleton ())
    gs = enum1 @g (singleton ())
    entry f1 = fmap (length f1, ) gs

runTemplate
  :: forall f g a.
     (Enum1 f, Foldable f, Traversable g)
  => Template f g
  -> FromN (f a -> g a)
runTemplate (MkTemplate t) = toNat <$> traverse inner t
  where
    inner (n, g1) =
      let vars = generate n id
      in traverse (const vars) g1
    toNat table fa =
      let args = foldMap singleton fa
          gi = table ! fromEnum1 @f 1 (const 0) fa
      in (args !) <$> gi

------------------------------------------

allPures :: forall f a. (Enum1 f, Functor f) => FromN (a -> f a)
allPures = fmap (\f1 -> (<$ f1)) (enum1 @f (singleton ()))
