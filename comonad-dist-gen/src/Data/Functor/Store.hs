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
  -- * (Indexed) Store Comonad 
  C(..),
  extract', duplicate',
  type Store,

  -- ** Manipulating Store comonads
  pos, peek,
  mapPos, mapPort,
  compF, decompF,

  -- * Lenses are natural transformations between Store comonads 
  Lens(..),
  (|>), idLens,
  toLens, fromLens,

  -- * Encode finitary lenses into numbers
  LensCode(..),
  encodeLens,
  decodeLens,
  decodeLens',
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
import Data.Foldable (toList)

-- * Store Comonad

-- | (Indexed) Store Comonad
data C s p x = C s (p -> x)
  deriving Functor

extract' :: C s s x -> x
extract' (C s f) = f s

duplicate' :: C s s'' x -> C s s' (C s' s'' x)
duplicate' (C s f) = C s $ \s' -> C s' f


-- The 'Store' comonad is a special case of @C s p@: when @s ~ p@.
type Store s = C s s

-- | = @Comonad ('Store' s)@
instance (s ~ p) => Comonad (C s p) where
  extract = extract'
  duplicate = duplicate'

mapPos :: (s -> s') -> C s p x -> C s' p x
mapPos g (C s f) = C (g s) f

mapPort :: (p' -> p) -> C s p x -> C s p' x
mapPort g (C s f) = C s (f . g)

pos :: C s p x -> s
pos (C s _) = s

peek :: C s p x -> p -> x
peek (C _ f) = f

-- | Composition of two @C _ _@ is isomorphic to another @C _ _@
compF :: forall s p s' p' x. C s p (C s' p' x) -> C (C s p s') (p,p') x
compF cc = C (C (pos cc) (pos . peek cc)) (\(p,p') -> peek (peek cc p) p')

decompF :: forall s p s' p' x. C (C s p s') (p,p') x -> C s p (C s' p' x)
decompF c = C (pos (pos c)) $ \p -> C (peek (pos c) p) (\p' -> peek c (p,p'))

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

-- | 'Lens' for 'Finitary' types, encoded as bunch of 'Integer's.
newtype LensCode = LensCode [(Integer, Integer)]
  deriving (Show, Read, Eq, Ord)

-- | Encode lens as LensCode
encodeLens :: (Finitary s, Finitary p, Finitary s', Finitary p') => Lens s p s' p' -> LensCode
encodeLens l = LensCode $ (bimap (getFinite . toFinite) (getFinite . toFinite)) <$> toList (lensToFn l)

-- | (Fallible) construction of Lens from LensCode
decodeLens :: (Finitary s, Finitary p, Finitary s', Finitary p') => LensCode -> Maybe (Lens s p s' p')
decodeLens (LensCode input) = do
  vec <- SV.fromList input
  vecFinite <- traverse (\(x,y) -> (,) <$> packFinite x <*> packFinite y) vec
  pure $ fnToLens $ (\(sCode, fnCode) -> (fromFinite sCode, fromFinite fnCode)) <$> vecToFn vecFinite

-- | Fail-with-'error' version of 'decodeLens'
decodeLens' :: (Finitary s, Finitary p, Finitary s', Finitary p') => LensCode -> Lens s p s' p'
decodeLens' input = case decodeLens input of
  Nothing -> error "decodeLens': invalid code"
  Just enc -> enc
