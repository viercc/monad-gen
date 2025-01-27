{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module StoreDistributiveLaw(
  Dist,
  DistLens,
  distToLens,
  distFromLens,

  Equals(..),
  law1, law2, law3, law4,
  law1Lens, law2Lens, law3Lens, law4Lens,
  checkAllLaws,

  generateCandidateLenses,

  module Data.Functor.Store,
) where

import Control.Comonad
import Data.Finitary ( inhabitants, Finitary )
import Data.Finitary.Extra ( sequenceFn )

import Data.Functor.Store

-- * Distributive law and their laws

-- Type of distributive laws
type Dist s t = forall x. Store s (Store t x) -> Store t (Store s x)

-- Dist as lens
type DistLens s t = Lens (C s s t) (s,t) (C t t s) (t,s)

distToLens :: Dist s t -> DistLens s t
distToLens f = toLens (compF . f . decompF)

distFromLens :: DistLens s t -> Dist s t
distFromLens l = decompF . fromLens l . compF

-- Type of "equation" on a
data Equals a = Equals { lhs :: a, rhs :: a }

-- Distributive law laws

law1 :: Dist s t -> Equals (C s s (C t t x) -> C s s x)
law1 dist = Equals (extract . dist) (fmap extract)

law2 :: Dist s t -> Equals (C s s (C t t x) -> C t t x)
law2 dist = Equals (fmap extract . dist) extract

law3 :: Dist s t -> Equals (C s s (C t t x) -> C t t (C t t (C s s x)))
law3 dist = Equals (duplicate . dist) (fmap dist . dist . fmap duplicate)

law4 :: Dist s t -> Equals (C s s (C t t x) -> C t t (C s s (C s s x)))
law4 dist = Equals (fmap duplicate . dist) (dist . fmap dist . duplicate)

-- Laws in terms of lens

law1Lens :: forall s t. DistLens s t -> Equals (Lens (C s s t) (s,t) s s)
law1Lens dLens = Equals lhsLens rhsLens
  where
    dist :: Dist s t
    dist = distFromLens dLens
    lhsLens = toLens (lhs (law1 dist) . decompF)
    rhsLens = toLens (rhs (law1 dist) . decompF)

law2Lens :: forall s t. DistLens s t -> Equals (Lens (C s s t) (s,t) t t)
law2Lens dLens = Equals lhsLens rhsLens
  where
    dist :: Dist s t
    dist = distFromLens dLens
    lhsLens = toLens (lhs (law2 dist) . decompF)
    rhsLens = toLens (rhs (law2 dist) . decompF)

law3Lens :: forall s t. DistLens s t -> Equals (Lens (C s s t) (s,t) (C (C t t t) (t, t) s) ((t, t), s))
law3Lens dLens = Equals lhsLens rhsLens
  where
    dist :: Dist s t
    dist = distFromLens dLens
    lhsLens = toLens (compF . compF . lhs (law3 dist) . decompF)
    rhsLens = toLens (compF . compF . rhs (law3 dist) . decompF)

law4Lens :: forall s t. DistLens s t -> Equals  (Lens (C s s t) (s,t) (C (C t t s) (t, s) s) ((t, s), s))
law4Lens dLens = Equals lhsLens rhsLens
  where
    dist :: Dist s t
    dist = distFromLens dLens
    lhsLens = toLens (compF . compF . lhs (law4 dist) . decompF)
    rhsLens = toLens (compF . compF . rhs (law4 dist) . decompF)

check :: Eq a => Equals a -> Bool
check (Equals a1 a2) = a1 == a2

checkAllLaws :: (Finitary s, Finitary t) => DistLens s t -> Bool
checkAllLaws l =
     check (law1Lens l)
  && check (law2Lens l)
  && check (law3Lens l)
  && check (law4Lens l)

{-
Even for this smallest case, simply enumerating every lenses
is not possible.

  ghci> :kind! Cardinality (DistLens A B)
  Cardinality (DistLens A B) :: GHC.Num.Natural.Natural
  = 309485009821345068724781056
-}

generateCandidateLenses :: (Finitary s, Finitary t) => () -> [DistLens s t]
generateCandidateLenses _ = map Lens $ sequenceFn $ \sst -> do
  let (C s0 f) = sst
  let t0 = f s0
  f' <- sequenceFn $ \t' -> if t' == t0 then [s0] else inhabitants
  putPart <- sequenceFn  $ \case
    (t,s) | t == t0 -> [ (s, f s) ]
          | s == f' t -> [ (s0, t) ]
          | otherwise -> inhabitants
  pure (C t0 f', putPart)
