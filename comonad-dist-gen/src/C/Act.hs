{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module C.Act(
  Act(..),
  toSt, fromSt,

  distDefault,
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
import Data.Group
import C.St (St (..))

-- Regular monoid action comonad
newtype Act g x = Act { unAct :: C g g x }
    deriving stock (Functor)
    deriving newtype (Eq, Finitary)

instance Monoid g => Comonad (Act g) where
  extract = extract' . unAct
  duplicate = fmap Act . Act . duplicate' . unAct

instance IsC g g (Act g)

extract' :: Monoid g => C g g x -> x
extract' (C _ f) = f mempty

duplicate' :: Semigroup g => C g g x -> C g g (C g g x)
duplicate' (C g0 f) = C g0 $ \g1 -> C (g1 <> g0) (f . (<> g1))

toSt :: Group g => Act g x -> St g x
toSt (Act (C g0 f)) = St (C g0 $ \g1 -> f (g1 ~~ g0))

fromSt :: Group g => St g x -> Act g x
fromSt (St (C g0 f)) = Act (C g0 $ \g1 -> f (g1 <> g0))

-- * Act distributive laws

distDefault :: (Comonad w) => Dist w (Act g)
distDefault w = Act $ C (pos' (extract w)) $ \g1 -> peek' g1 <$> w
  where
    pos' = pos . unAct
    peek' g1 (Act (C _ f)) = f g1

-- Dist as lens
type DistLens s t = Lens (C s s t) (s,t) (C t t s) (t,s)

distToLens :: Dist (Act s) (Act t) -> DistLens s t
distToLens f = toLens (toC . Compose . f . getCompose . fromC)

distFromLens :: DistLens s t -> Dist (Act s) (Act t)
distFromLens l = getCompose . fromC . fromLens l . toC . Compose

-- Laws in terms of lens

toLens21 :: (forall x. Act s (Act t x) -> Act u x) -> Lens (C s s t) (s,t) u u
toLens21 f = toLens (toC . f . getCompose . fromC)

toLens23 :: (forall x. Act s (Act t x) -> Act u1 (Act u2 (Act u3 x)))
  -> (Lens (C s s t) (s, t) (C (C u1 u1 u2) (u1, u2) u3) ((u1, u2), u3))
toLens23 f = toLens (toC . Compose . Compose . f . getCompose . fromC)

law1Lens :: forall s t. (Monoid s, Monoid t) => DistLens s t -> Equals (Lens (C s s t) (s,t) s s)
law1Lens dLens = toLens21 <$> law1 (distFromLens dLens)

law2Lens :: forall s t. (Monoid s, Monoid t) => DistLens s t -> Equals (Lens (C s s t) (s,t) t t)
law2Lens dLens = toLens21 <$> law2 (distFromLens dLens)

law3Lens :: forall s t. (Monoid s, Monoid t) => DistLens s t -> Equals (Lens (C s s t) (s, t) (C (C t t t) (t, t) s) ((t, t), s))
law3Lens dLens = toLens23 <$> law3 (distFromLens dLens)

law4Lens :: forall s t. (Monoid s, Monoid t) => DistLens s t -> Equals  (Lens (C s s t) (s, t) (C (C t t s) (t, s) s) ((t, s), s))
law4Lens dLens = toLens23 <$> law4 (distFromLens dLens)

check :: Eq a => Equals a -> Bool
check (Equals a1 a2) = a1 == a2

checkAllLaws :: (Finitary s, Finitary t) => (Monoid s, Monoid t) => DistLens s t -> Bool
checkAllLaws l =
     check (law1Lens l)
  && check (law2Lens l)
  && check (law3Lens l)
  && check (law4Lens l)
