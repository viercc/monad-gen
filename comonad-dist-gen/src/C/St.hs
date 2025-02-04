{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module C.St(
  St(..),

  Dist,
  DistLens,
  distToLens,
  distFromLens,
  checkAllLaws
) where

import Control.Comonad

import Data.Finitary (Finitary)

import C

import Control.Comonad.DistributiveLaw
import Data.Functor.Compose (Compose(..))

-- Store comonad
newtype St s x = St { unSt :: C s s x }
    deriving stock (Functor)
    deriving newtype (Eq, Finitary)

instance Comonad (St s) where
  extract = extract' . unSt
  duplicate = fmap St . St . duplicate' . unSt

instance IsC s s (St s)

extract' :: C s s x -> x
extract' (C s f) = f s

duplicate' :: C s s'' x -> C s s' (C s' s'' x)
duplicate' (C s f) = C s $ \s' -> C s' f

-- * Store distributive laws

-- Dist as lens
type DistLens s t = Lens (C s s t) (s,t) (C t t s) (t,s)

distToLens :: Dist (St s) (St t) -> DistLens s t
distToLens f = toLens (toC . Compose . f . getCompose . fromC)

distFromLens :: DistLens s t -> Dist (St s) (St t)
distFromLens l = getCompose . fromC . fromLens l . toC . Compose

-- Laws in terms of lens

toLens21 :: (forall x. St s (St t x) -> St u x) -> Lens (C s s t) (s,t) u u
toLens21 f = toLens (toC . f . getCompose . fromC)

toLens23 :: (forall x. St s (St t x) -> St u1 (St u2 (St u3 x)))
  -> (Lens (C s s t) (s, t) (C (C u1 u1 u2) (u1, u2) u3) ((u1, u2), u3))
toLens23 f = toLens (toC . Compose . Compose . f . getCompose . fromC)

law1Lens :: forall s t. DistLens s t -> Equals (Lens (C s s t) (s,t) s s)
law1Lens dLens = toLens21 <$> law1 (distFromLens dLens)

law2Lens :: forall s t. DistLens s t -> Equals (Lens (C s s t) (s,t) t t)
law2Lens dLens = toLens21 <$> law2 (distFromLens dLens)

law3Lens :: forall s t. DistLens s t -> Equals (Lens (C s s t) (s, t) (C (C t t t) (t, t) s) ((t, t), s))
law3Lens dLens = toLens23 <$> law3 (distFromLens dLens)

law4Lens :: forall s t. DistLens s t -> Equals  (Lens (C s s t) (s, t) (C (C t t s) (t, s) s) ((t, s), s))
law4Lens dLens = toLens23 <$> law4 (distFromLens dLens)

check :: Eq a => Equals a -> Bool
check (Equals a1 a2) = a1 == a2

checkAllLaws :: (Finitary s, Finitary t) => DistLens s t -> Bool
checkAllLaws l =
     check (law1Lens l)
  && check (law2Lens l)
  && check (law3Lens l)
  && check (law4Lens l)
