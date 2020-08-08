{-# LANGUAGE DeriveFunctor #-}
module Data.Profunctor.Exhaust(
  Exhaust(..)
) where

import Data.Void

import Data.Profunctor
import Data.Profunctor.Cartesian

data Exhaust a b = Absurd (a -> Void)
                 | Exhaust ((b -> Bool) -> b)
  deriving (Functor)

instance Profunctor Exhaust where
  lmap l (Absurd f)  = Absurd (f . l)
  lmap _ (Exhaust g) = Exhaust g
  
  rmap _ (Absurd f)  = Absurd f
  rmap r (Exhaust s) = Exhaust $ \cond -> r $ s (cond . r)

instance Cartesian Exhaust where
  proUnit = Exhaust (\_ -> ())
  Absurd p  *** _         = Absurd (\(a,_) -> p a)
  Exhaust _ *** Absurd q  = Absurd (\(_,a') -> q a')
  Exhaust p *** Exhaust q = Exhaust pq
    where
      pq cond =
        let subQuery b = q $ \b' -> cond (b, b')
            bGot = p $ \b -> cond (b, subQuery b)
        in (bGot, subQuery bGot)

instance Cocartesian Exhaust where
  proEmpty = Absurd id
  Absurd p  +++ Absurd q  = Absurd $ either p q
  Absurd _  +++ Exhaust q = Exhaust $ \cond -> Right $ q (cond . Right)
  Exhaust p +++ Absurd _  = Exhaust $ \cond -> Left $ p (cond . Left)
  Exhaust p +++ Exhaust q = Exhaust $ \cond ->
    let x = Left $ p (cond . Left)
        y = Right $ q (cond . Right)
    in if cond x then x else y
