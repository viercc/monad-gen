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

-- * Free Cartesian profunctor

data FreeCartesian p a b =
      ProUnit b
    | forall b1 b2. ProMult (p a b1) (FreeCartesian p a b2) (b1 -> b2 -> b)

deriving instance Functor (FreeCartesian p a)

instance Applicative (FreeCartesian p a) where
    pure = ProUnit
    ProUnit x <*> qs = x <$> qs
    ProMult p ps op <*> qs = ProMult p (liftA2 (,) ps qs) (\b1 (b2, b') -> op b1 b2 b')

instance Profunctor p => Profunctor (FreeCartesian p) where
    lmap f fp = case fp of
        ProUnit b -> ProUnit b
        ProMult p ps op -> ProMult (lmap f p) (lmap f ps) op
    
    rmap = fmap

    dimap f g fp = case fp of
        ProUnit b -> ProUnit (g b)
        ProMult p ps op -> ProMult (lmap f p) (lmap f ps) (\b1 b2 -> g (op b1 b2))

instance Profunctor p => Cartesian (FreeCartesian p) where
    proUnit = ProUnit ()
    ProUnit a *** qs = dimap snd (a,) qs
    ProMult p ps op *** qs = ProMult (lmap fst p) (ps *** qs) (\b1 (b2, b') -> (op b1 b2, b'))

liftFreeCartesian :: Profunctor p => p :-> FreeCartesian p
liftFreeCartesian p = ProMult p (ProUnit ()) const

foldFreeCartesian :: Cartesian q => (p :-> q) -> FreeCartesian p :-> q
foldFreeCartesian _ (ProUnit b) = rmap (const b) proUnit
foldFreeCartesian handle (ProMult p ps op) = dimap (\a -> (a,a)) (uncurry op) (handle p *** foldFreeCartesian handle ps)

-- * Free Cocartesian profunctor

data FreeCocartesian p a b =
      ProEmpty (a -> Void)
    | forall a1 a2. ProSum (p a1 b) (FreeCocartesian p a2 b) (a -> Either a1 a2)

instance Profunctor p => Functor (FreeCocartesian p a) where
    fmap f ps = case ps of
        ProEmpty z -> ProEmpty z
        ProSum p ps' op -> ProSum (rmap f p) (rmap f ps') op

instance Profunctor p => Profunctor (FreeCocartesian p) where
    lmap f ps = case ps of
        ProEmpty z -> ProEmpty (z . f)
        ProSum p ps' op -> ProSum p ps' (op . f)
    
    rmap = fmap

    dimap f g ps = case ps of
        ProEmpty z -> ProEmpty (z . f)
        ProSum p ps' op -> ProSum (rmap g p) (rmap g ps') (op . f)

instance Profunctor p => Cocartesian (FreeCocartesian p) where
    proEmpty = ProEmpty id
    ProEmpty z +++ qs = dimap (either (absurd . z) id) Right qs
    ProSum p ps' op +++ qs = ProSum (rmap Left p) (ps' +++ qs) $
      either (fmap Left . op) (Right . Right)

liftFreeCocartesian :: Profunctor p => p :-> FreeCocartesian p
liftFreeCocartesian p = ProSum p (ProEmpty id) Left

foldFreeCocartesian :: (Cocartesian q) => (p :-> q) -> FreeCocartesian p :-> q
foldFreeCocartesian handle ps = case ps of
    ProEmpty z -> lmap z proEmpty
    ProSum p ps' op -> dimap op (either id id) (handle p +++ foldFreeCocartesian handle ps')

instance Cartesian p => Cartesian (FreeCocartesian p) where
    proUnit = liftFreeCocartesian proUnit
    ProEmpty z *** _ = ProEmpty (z . fst)
    ProSum p ps' op *** qs = dimap distR (either id id) $ distLeftFree p qs +++ (ps' *** qs)
      where
        distR (a, a') = case op a of
            Left a1 -> Left (a1, a')
            Right a2 -> Right (a2, a')

distLeftFree :: Cartesian p => p a b -> FreeCocartesian p a' b' -> FreeCocartesian p (a,a') (b,b')
distLeftFree _ (ProEmpty z) = ProEmpty (z . snd)
distLeftFree p (ProSum q qs' op) = ProSum (p *** q) (distLeftFree p qs') $ \(a, a') ->
    case op a' of
        Left a1' -> Left (a, a1')
        Right a2' -> Right (a, a2')

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