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

-- | Store functors and Lenses as transformation between store functors
module Data.Functor.Store(
  C(..),
  type Store,
  pos, peek,
  mapPos, mapPort,
  compF, decompF,
  assocF, unassocF,

  Lens(..),
  (|>), idLens,
  toLens, fromLens,

  LensEnc(..),
  encodeLens,
  decodeLens,
  makeLensEnc,
  makeLensEnc'
) where

import Data.Coerce (coerce)
import Data.Bifunctor (Bifunctor(..))

import GHC.TypeNats (type (*), type (^))

import Control.Comonad
import Data.Finitary
import Data.Finitary.Extra
import Data.Finite (Finite, getFinite, packFinite)

import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as SV
import Data.Functor.Classes ( showsBinaryWith, showsUnaryWith )

-- * (Generalized) Store Comonad

data C s p x = C s (p -> x)
  deriving Functor

instance (s ~ p) => Comonad (C s p) where
  extract (C s f) = f s
  duplicate (C s f) = C s $ \s' -> C s' f

type Store s = C s s

mapPos :: (s -> s') -> C s p x -> C s' p x
mapPos g (C s f) = C (g s) f

mapPort :: (p' -> p) -> C s p x -> C s p' x
mapPort g (C s f) = C s (f . g)

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

newtype LensEnc s p s' p' = LensEnc (Vector (Cardinality s) (Finite (Cardinality s'), Finite (Cardinality p ^ Cardinality p')))
  deriving (Eq, Ord)

instance (Finitary s, Finitary p, Finitary s', Finitary p) => Show (LensEnc s p s' p') where
  showsPrec p (LensEnc v) = showsUnaryWith showsPrec "makeLensEnc'" p (bimap getFinite getFinite <$> SV.toList v)

encodeLens :: (Finitary s, Finitary p, Finitary s', Finitary p') => Lens s p s' p' -> LensEnc s p s' p'
encodeLens l = LensEnc $ (\(s', fn) -> (toFinite s', toFinite fn)) <$> fnToVec (lensToFn l)

decodeLens :: (Finitary s, Finitary p, Finitary s', Finitary p') => LensEnc s p s' p' -> Lens s p s' p'
decodeLens (LensEnc v) = fnToLens $ (\(sCode, fnCode) -> (fromFinite sCode, fromFinite fnCode)) <$> vecToFn v

-- | (Fallible) construction of LensEnc from list of 'Integer's.
makeLensEnc :: (Finitary s, Finitary p, Finitary s', Finitary p') => [(Integer, Integer)] -> Maybe (LensEnc s p s' p')
makeLensEnc input = do
  finiteList <- traverse (\(x,y) -> (,) <$> packFinite x <*> packFinite y) input
  LensEnc <$> SV.fromList finiteList

-- | Fail-with-'error' version of 'makeLensEnc'
makeLensEnc' :: (Finitary s, Finitary p, Finitary s', Finitary p') => [(Integer, Integer)] -> LensEnc s p s' p'
makeLensEnc' input = case makeLensEnc input of
  Nothing -> error "makeLensEnc': invalid"
  Just enc -> enc
