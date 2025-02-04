{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
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
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DefaultSignatures #-}

-- | Store functors and Lenses as transformation between store functors
module C(
  -- * (Indexed) Store Comonad 
  C(..),

  -- ** Manipulating Store comonads
  pos, peek,
  mapC,
  compF, decompF,

  -- * Functor representatable as C
  IsC(..),

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

import Data.Coerce (coerce, Coercible)
import Data.Bifunctor (Bifunctor(..))

import GHC.TypeNats (type (*), type (^))

import Data.Finitary
import Data.Finitary.Extra
import Data.Finite (getFinite, packFinite)

import qualified Data.Vector.Sized as SV
import Data.Functor.Classes ( showsBinaryWith, showsUnaryWith )
import Data.Foldable (toList)
import Data.Kind (Type)
import Data.Functor.Compose

-- * Store Comonad

-- | (Indexed) Store Comonad
data C s p x = C s (p -> x)
  deriving Functor

mapC :: (s -> s') -> (p' -> p) -> C s p x -> C s' p' x
mapC gs gp (C s f) = C (gs s) (f . gp)

pos :: C s p x -> s
pos (C s _) = s

peek :: C s p x -> p -> x
peek (C _ f) = f

-- | Composition of two @C _ _@ is isomorphic to another @C _ _@
compF :: forall s p s' p' x. C s p (C s' p' x) -> C (C s p s') (p,p') x
compF cc = C (C (pos cc) (pos . peek cc)) (\(p,p') -> peek (peek cc p) p')

decompF :: forall s p s' p' x. C (C s p s') (p,p') x -> C s p (C s' p' x)
decompF c = C (pos (pos c)) $ \p -> C (peek (pos c) p) (\p' -> peek c (p,p'))

class Functor f => IsC s p (f :: Type -> Type) | f -> s p where
  toC :: f x -> C s p x
  default toC :: Coercible (f x) (C s p x) => f x -> C s p x
  toC = coerce

  fromC :: C s p x -> f x
  default fromC :: Coercible (C s p x) (f x) => C s p x -> f x
  fromC = coerce

instance IsC s p (C s p) where
  toC = id
  fromC = id

instance (IsC s p f, IsC s' p' g) => IsC (C s p s') (p,p') (Compose f g) where
  toC = compF . toC . fmap toC . getCompose
  fromC = Compose . fmap fromC . fromC . decompF

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
