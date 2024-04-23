{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
module Data.Profunctor.Cartesian.FreeBicartesian(
  FreeBicartesian(..),
  liftFreeBicartesian,
  foldFreeBicartesian,

  FreeBicartesianD(..),
  liftFreeBicartesianD,
  foldFreeBicartesianD
) where

import Data.Profunctor (Profunctor(..), (:->))
import Data.Profunctor.Cartesian
import Data.Profunctor.Monad

import Data.Profunctor.Cartesian.Free

-- * Free bicartesian, no assumed distributivity

newtype FreeBicartesian p a b = FreeBicartesian {
    runFreeBicartesian :: forall q. (Cartesian q, Cocartesian q) => (p :-> q) -> q a b
  }

instance Functor (FreeBicartesian p a) where
  fmap = rmap

instance Profunctor (FreeBicartesian p) where
  dimap f g (FreeBicartesian fp) = FreeBicartesian $ \ret -> dimap f g (fp ret)
  lmap f (FreeBicartesian fp) = FreeBicartesian $ \ret -> lmap f (fp ret)
  rmap g (FreeBicartesian fp) = FreeBicartesian $ \ret -> rmap g (fp ret)


instance Cartesian (FreeBicartesian p) where
  proUnit = FreeBicartesian (const proUnit)
  FreeBicartesian fp1 *** FreeBicartesian fp2
    = FreeBicartesian \ret -> fp1 ret *** fp2 ret

instance Cocartesian (FreeBicartesian p) where
  proEmpty = FreeBicartesian (const proEmpty)
  FreeBicartesian fp1 +++ FreeBicartesian fp2
    = FreeBicartesian \ret -> fp1 ret +++ fp2 ret

liftFreeBicartesian :: p :-> FreeBicartesian p
liftFreeBicartesian p = FreeBicartesian \ret -> ret p

foldFreeBicartesian :: (Cartesian q, Cocartesian q) => (p :-> q) -> FreeBicartesian p :-> q
foldFreeBicartesian pq fp = runFreeBicartesian fp pq

instance ProfunctorFunctor FreeBicartesian where
  promap pq (FreeBicartesian fp) = FreeBicartesian \ret -> fp (ret . pq)

instance ProfunctorMonad FreeBicartesian where
  proreturn = liftFreeBicartesian
  projoin = foldFreeBicartesian id

-- * Free distributive bicartesian

newtype FreeBicartesianD p a b = FreeBicartesianD
  { runFreeBicartesianD :: FreeCocartesian (FreeCartesian p) a b }

instance Profunctor p => Functor (FreeBicartesianD p a) where
  fmap = rmap

deriving newtype instance Profunctor p => Profunctor (FreeBicartesianD p)
deriving newtype instance Profunctor p => Cartesian (FreeBicartesianD p)
deriving newtype instance Profunctor p => Cocartesian (FreeBicartesianD p)

liftFreeBicartesianD :: Profunctor p => p :-> FreeBicartesianD p
liftFreeBicartesianD = FreeBicartesianD . liftFreeCocartesian . liftFreeCartesian

foldFreeBicartesianD :: (Cartesian q, Cocartesian q) => (p :-> q) -> FreeBicartesianD p :-> q
foldFreeBicartesianD handle = foldFreeCocartesian (foldFreeCartesian handle) . runFreeBicartesianD

instance ProfunctorFunctor FreeBicartesianD where
    promap pq = FreeBicartesianD . promap (promap pq) . runFreeBicartesianD

instance ProfunctorMonad FreeBicartesianD where
    proreturn = liftFreeBicartesianD
    projoin = foldFreeBicartesianD id
