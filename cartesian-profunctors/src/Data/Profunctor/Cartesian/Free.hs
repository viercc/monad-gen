{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
module Data.Profunctor.Cartesian.Free where

import Data.Void (Void, absurd)
import Data.Profunctor (Profunctor(..), (:->))
import Data.Profunctor.Cartesian
import Data.Bifunctor (Bifunctor(..))

-- * Free Cartesian profunctor

data FreeCartesian p a b =
      ProUnit b
    | forall a1 a2 b1 b2. ProMult (p a1 b1) (FreeCartesian p a2 b2) (a -> (a1, a2)) ((b1, b2) -> b)

deriving instance Functor (FreeCartesian p a)

instance Applicative (FreeCartesian p a) where
    pure = ProUnit
    p <*> q = dimap (\a -> (a,a)) (\(f,x) -> f x) $ p *** q

instance Profunctor (FreeCartesian p) where
    dimap f g fp = case fp of
        ProUnit b -> ProUnit (g b)
        ProMult p ps opA opB -> ProMult p ps (opA . f) (g . opB)

instance Cartesian (FreeCartesian p) where
    proUnit = ProUnit ()
    ProUnit a *** qs = dimap snd (a,) qs
    ProMult p ps opA opB *** qs = ProMult p (ps *** qs) (assocTup . first opA) (first opB . unassocTup)

assocTup :: ((a,b), c) -> (a, (b,c))
assocTup ((a,b), c) = (a, (b,c))

unassocTup :: (a, (b,c)) ->  ((a,b), c)
unassocTup (a, (b,c)) = ((a,b), c)

liftFreeCartesian :: p :-> FreeCartesian p
liftFreeCartesian p = ProMult p (ProUnit ()) (, ()) fst

foldFreeCartesian :: Cartesian q => (p :-> q) -> FreeCartesian p :-> q
foldFreeCartesian _ (ProUnit b) = rmap (const b) proUnit
foldFreeCartesian handle (ProMult p ps opA opB) = dimap opA opB (handle p *** foldFreeCartesian handle ps)

-- * Free Cocartesian profunctor

data FreeCocartesian p a b =
      ProEmpty (a -> Void)
    | forall a1 a2 b1 b2. ProSum (p a1 b1) (FreeCocartesian p a2 b2) (a -> Either a1 a2) (Either b1 b2 -> b)

instance Profunctor p => Functor (FreeCocartesian p a) where
    fmap f ps = case ps of
        ProEmpty z -> ProEmpty z
        ProSum p ps' opA opB -> ProSum p ps' opA (f . opB)
instance Profunctor p => Profunctor (FreeCocartesian p) where
    dimap f g ps = case ps of
        ProEmpty z -> ProEmpty (z . f)
        ProSum p ps' opA opB -> ProSum p ps' (opA . f) (g . opB)

instance Profunctor p => Cocartesian (FreeCocartesian p) where
    proEmpty = ProEmpty id
    ProEmpty z +++ qs = dimap (either (absurd . z) id) Right qs
    ProSum p ps' opA opB +++ qs = ProSum p (ps' +++ qs) (assocEither . first opA) (first opB . unassocEither)

assocEither :: Either (Either a b) c -> Either a (Either b c)
assocEither = either (second Left) (Right . Right)

unassocEither :: Either a (Either b c) -> Either (Either a b) c
unassocEither = either (Left . Left) (first Right)

liftFreeCocartesian :: p :-> FreeCocartesian p
liftFreeCocartesian p = ProSum p (ProEmpty id) Left (either id absurd)

foldFreeCocartesian :: (Cocartesian q) => (p :-> q) -> FreeCocartesian p :-> q
foldFreeCocartesian handle ps = case ps of
    ProEmpty z -> lmap z proEmpty
    ProSum p ps' opA opB -> dimap opA opB (handle p +++ foldFreeCocartesian handle ps')

instance Cartesian p => Cartesian (FreeCocartesian p) where
    proUnit = liftFreeCocartesian proUnit
    ProEmpty z *** _ = ProEmpty (z . fst)
    ProSum p ps' opA opB *** qs = dimap (distR . first opA) (first opB . undistR) $ distLeftFree p qs +++ (ps' *** qs)

distLeftFree :: Cartesian p => p a b -> FreeCocartesian p a' b' -> FreeCocartesian p (a,a') (b,b')
distLeftFree _ (ProEmpty z) = ProEmpty (z . snd)
distLeftFree p (ProSum q qs' opA opB) = ProSum (p *** q) (distLeftFree p qs') (distL . second opA) (second opB . undistL)

distR :: (Either a1 a2, b) -> Either (a1, b) (a2, b)
distR (ea, b) = bimap (, b) (, b) ea

undistR :: Either (a1, b) (a2, b) -> (Either a1 a2, b)
undistR = either (first Left) (first Right)

distL :: (a, Either b1 b2) -> Either (a, b1) (a, b2)
distL (a,b) = bimap (a,) (a,) b

undistL :: Either (a, b1) (a, b2) -> (a, Either b1 b2)
undistL = either (second Left) (second Right)

-- * Free Bicartesian

newtype FreeBicartesian p a b = FreeBicartesian
  { runFreeBicartesian :: FreeCocartesian (FreeCartesian p) a b }

deriving newtype instance Profunctor p => Profunctor (FreeBicartesian p)
deriving newtype instance Profunctor p => Cartesian (FreeBicartesian p)
deriving newtype instance Profunctor p => Cocartesian (FreeBicartesian p)

liftFreeBicartesian :: Profunctor p => p :-> FreeBicartesian p
liftFreeBicartesian = FreeBicartesian . liftFreeCocartesian . liftFreeCartesian

foldFreeBicartesian :: (Cartesian q, Cocartesian q) => (p :-> q) -> FreeBicartesian p :-> q
foldFreeBicartesian handle = foldFreeCocartesian (foldFreeCartesian handle) . runFreeBicartesian