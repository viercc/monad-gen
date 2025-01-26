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
  C(..),
  pos, peek,
  mapPos, mapPort,
  compF, decompF,
  assocF, unassocF,

  Lens(..),
  (|>), idLens,
  toLens, fromLens,

  Dist,
  DistLens,
  distToLens,
  distFromLens,

  A(..), B(..),
  candidateLenses,
  lawfulDistLenses,

  LensEnc(..),
  encodeLens,
  decodeLens,
) where

import Control.Comonad
import Data.Finitary
import Data.Finitary.Extra
import GHC.TypeNats (type (*), type (^))
import Data.Bifunctor (Bifunctor(..))
import Data.Coerce (coerce)
import Data.Bool (bool)
import Data.Functor.Classes (showsUnaryWith, showsBinaryWith)
import Control.Monad (guard)
import Data.Vector.Sized (Vector)
import Data.Finite (Finite)

-- * (Generalized) Store Comonad

data C s p x = C s (p -> x)
  deriving Functor

mapPos :: (s -> s') -> C s p x -> C s' p x
mapPos g (C s f) = C (g s) f

mapPort :: (p' -> p) -> C s p x -> C s p' x
mapPort g (C s f) = C s (f . g)

instance (s ~ p) => Comonad (C s p) where
  extract (C s f) = f s
  duplicate (C s f) = C s $ \s' -> C s' f

type Store s = C s s

pos :: C s p x -> s
pos (C s _) = s

peek :: C s p x -> p -> x
peek (C _ f) = f

compF :: forall s p s' p' x. C s p (C s' p' x) -> C (C s p s') (p,p') x
compF cc = C (C (pos cc) (pos . peek cc)) (\(p,p') -> peek (peek cc p) p')

decompF :: forall s p s' p' x. C (C s p s') (p,p') x -> C s p (C s' p' x)
decompF c = C (pos (pos c)) $ \p -> C (peek (pos c) p) (\p' -> peek c (p,p'))

assocF :: C (C s p (C s' p' s'')) (p,(p',p'')) x -> C (C (C s p s') (p, p') s'') ((p, p'), p'') x
assocF = compF . compF . fmap decompF . decompF

unassocF :: C (C (C s p s') (p, p') s'') ((p, p'), p'') x -> C (C s p (C s' p' s'')) (p,(p',p'')) x
unassocF = compF . fmap compF . decompF . decompF

-- * Lens <-> Natural transformation between (C _ _)

newtype Lens s p s' p' = Lens { unLens :: s -> (s', p' -> p) }

(|>) :: Lens s p s' p' -> Lens s' p' s'' p'' -> Lens s p s'' p''
l1 |> l2 = Lens $ \s ->
    let (s', g) = unLens l1 s
        (s'', h) = unLens l2 s'
    in (s'', g . h)

idLens :: Lens s p s p
idLens = Lens $ \s -> (s, id)

toLens :: (forall x. C s p x -> C s' p' x) -> Lens s p s' p'
toLens f = Lens {
    unLens = \s -> case f (C s id) of
      C s' g -> (s', g)
  }

fromLens :: Lens s p s' p' -> C s p x -> C s' p' x
fromLens lens (C s f) = case unLens lens s of
  (s', g) -> C s' (f . g)

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

-- * Exhaustive search

instance (Eq s, Finitary p, Eq x) => Eq (C s p x) where
  C s1 f1 == C s2 f2 = s1 == s2 && Fn f1 == Fn f2

instance (Finitary s, Finitary p, Finitary x) => Finitary (C s p x) where
  type Cardinality (C s p x) = Cardinality s * (Cardinality x ^ Cardinality p)

  fromFinite k = case fromFinite k of
    (s, fn) -> C s (apply fn)
  
  toFinite (C s f) = toFinite (s, Fn f)

instance (Show s, Finitary p, Show p, Show x) => Show (C s p x) where
  showsPrec p (C s f) = showsBinaryWith showsPrec (\_ fn -> (showFn fn ++)) "C" p s f

instance (Finitary s, Eq p, Eq s', Finitary p') => Eq (Lens s p s' p') where
  l1 == l2 = lensToFn l1 == lensToFn l2

lensToFn :: Lens s p s' p' -> Fn s (s', Fn p' p)
lensToFn = coerce

fnToLens :: Fn s (s', Fn p' p) -> Lens s p s' p'
fnToLens = coerce

instance (Finitary s, Finitary p, Finitary s', Finitary p') => Finitary (Lens s p s' p') where
  type Cardinality (Lens s p s' p') = (Cardinality s' * (Cardinality p ^ Cardinality p')) ^ Cardinality s

  fromFinite = fnToLens . fromFinite
  toFinite = toFinite . lensToFn

instance (Finitary s, Show s, Show p, Show s', Finitary p', Show p')
  => Show (Lens s p s' p') where
  showsPrec p l = showsUnaryWith showsPrec "fnToLens" p (lensToFn l)

-- * Trying smallest nontrivial case: |s| = |t| = 2

newtype A = A Bool
  deriving newtype (Eq, Finitary)

instance Show A where
  show (A b) = 'A' : bool "₀" "₁" b

newtype B = B Bool
  deriving newtype (Eq, Finitary)

instance Show B where
  show (B b) = 'B' : bool "₀" "₁" b

{-
Even for this smallest case, simply enumerating every lenses
is not possible.

  ghci> :kind! Cardinality (DistLens A B)
  Cardinality (DistLens A B) :: GHC.Num.Natural.Natural
  = 309485009821345068724781056
-}

sequenceFn :: (Finitary a, Applicative m) => (a -> m b) -> m (a -> b)
sequenceFn = fmap apply . sequenceA . Fn

check :: Eq a => Equals a -> Bool
check (Equals a1 a2) = a1 == a2

lawfulDistLenses :: [DistLens A B] -> [DistLens A B]
lawfulDistLenses candidates =
  [ distLens
    | distLens <- candidates
    , check (law1Lens distLens)
    , check (law2Lens distLens)
    , check (law3Lens distLens)
    , check (law4Lens distLens)
  ]

candidateLenses :: () -> [DistLens A B]
candidateLenses _ = map Lens $ sequenceFn $ \sst -> do
  let (C s0 f) = sst
  let t0 = f s0
  f' <- sequenceFn $ \t' -> if t' == t0 then [s0] else inhabitants
  putPart <- sequenceFn  $ \case
    (t,s) | t == t0 -> [ (s, f s) ]
          | s == f' t -> [ (s0, t) ]
          | otherwise -> inhabitants
  pure (C t0 f', putPart)

newtype LensEnc s p s' p' = LensEnc (Vector (Cardinality s) (Finite (Cardinality s'), Finite (Cardinality p ^ Cardinality p')))
  deriving (Show, Eq, Ord)

encodeLens :: (Finitary s, Finitary p, Finitary s', Finitary p') => Lens s p s' p' -> LensEnc s p s' p'
encodeLens l = LensEnc $ (\(s', fn) -> (toFinite s', toFinite fn)) <$> fnToVec (lensToFn l)

decodeLens :: (Finitary s, Finitary p, Finitary s', Finitary p') => LensEnc s p s' p' -> Lens s p s' p'
decodeLens (LensEnc v) = fnToLens $ (\(sCode, fnCode) -> (fromFinite sCode, fromFinite fnCode)) <$> vecToFn v