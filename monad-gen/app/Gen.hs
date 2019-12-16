{-# LANGUAGE ScopedTypeVariables, TypeOperators, TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE KindSignatures #-}
module Gen(
  skolem, skolem2, skolem3,
  
  fIdx, allPures,

  Template(),
  enumTemplates,
  runTemplate
) where

import Data.Kind

import Data.Functor.Compose
import Control.Monad.State

import GHC.Generics

import Data.PTraversable
import Data.Functor.Contravariant.Divisible (conquer)
import Data.Functor.Numbering
import Data.Functor.Contravariant.CoNumbering
import Util

var :: Compose FromN (State Int) Int
var = Compose $ singleton (state (\i -> (i, i+1)))

skolem :: forall m. (PTraversable m) => FromN (m Int)
skolem = fmap fillIn . getCompose $ enum1 var
  where fillIn mx = evalState mx 0

skolem2 :: forall m. (PTraversable m) => FromN (m (m Int))
skolem2 = fmap unComp1 (skolem @(m :.: m))

skolem3 :: forall m. (PTraversable m) => FromN (m (m (m Int)))
skolem3 = fmap (fmap unComp1 . unComp1) (skolem @(m :.: m :.: m))

------------------------------------------

-- fs :: FromN (f ())
-- fs = enum1 (singleton ())
-- 
-- fIdx <$> fs = iota (size1 @f 1)
-- (\f -> fs ! (fIdx f)) = id :: f () -> f ()
fIdx :: forall f a. (PTraversable f) => f a -> Int
fIdx = getIndex (coenum1 @f conquer)

allPures :: forall f a. (PTraversable f) => FromN (a -> f a)
allPures = fmap (\f1 -> (<$ f1)) (enum1 @f (singleton ()))

-----------------------------------

newtype Template (f :: Type -> Type) g = MkTemplate (FromN (Int, g ()))

enumTemplates
  :: forall f g.
     (PTraversable f, PTraversable g)
  => FromN (Template f g)
enumTemplates = coerceMap MkTemplate (traverse entry fs)
  where
    fs = enum1 @f (singleton ())
    gs = enum1 @g (singleton ())
    entry f1 = fmap (length f1, ) gs

runTemplate
  :: forall f g a.
     (PTraversable f, PTraversable g)
  => Template f g
  -> FromN (f a -> g a)
runTemplate (MkTemplate t) = toNat <$> traverse inner t
  where
    inner (n, g1) =
      let vars = iota n
      in traverse (const vars) g1
    toNat table fa =
      let args = foldMap singleton fa
          gi = table ! fIdx fa
      in (args !) <$> gi
