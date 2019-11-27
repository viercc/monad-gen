{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Transparent(
  Transparent(..),
  eqDefault,
  compareDefault,
  enumList,
  enum,
  search
) where

import Data.Coerce

import Data.Void

import Control.Applicative
import Data.Functor.Contravariant
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker

import Data.Profunctor
import Data.Profunctor.Cartesian

import Internal.AuxProfunctors

class (Eq x, Ord x) => Transparent x where
  describe :: (Cartesian p, Cocartesian p)
           => p x x

eqDefault :: forall x. Transparent x => x -> x -> Bool
eqDefault = coerce $ describe @x @EquivalenceP

compareDefault :: forall x. Transparent x => x -> x -> Ordering
compareDefault = coerce $ describe @x @ComparisonP

enumList :: forall x. (Transparent x) => [x]
enumList = coerce $ describe @x @(Joker [])

enum :: (Transparent x, Alternative f) => f x
enum = lowerCoYoJoker describe

search :: Transparent x => (x -> Bool) -> Maybe x
search cond = case describe of
  Absurd _  -> Nothing
  Exhaust p -> let x = p cond
               in if cond x then Just x else Nothing

data Exhaust a b = Absurd (a -> Void)
                 | Exhaust ((b -> Bool) -> b)

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

instance Transparent Void where
  describe = proEmpty

instance Transparent () where
  describe = proUnit

instance (Transparent x, Transparent y) => Transparent (Either x y) where
  describe = describe +++ describe

instance (Transparent x, Transparent y) => Transparent (x,y) where
  describe = describe *** describe

instance (Transparent x1, Transparent x2, Transparent x3)
         => Transparent (x1,x2,x3) where
  describe = dimap l r $ describe *** describe
    where
      l (x1,x2,x3) = (x1,(x2,x3))
      r (x1,(x2,x3)) = (x1,x2,x3)

instance (Transparent x1, Transparent x2, Transparent x3, Transparent x4)
         => Transparent (x1,x2,x3,x4) where
  describe = dimap l r $ describe *** describe
    where
      l (x1,x2,x3,x4) = (x1,(x2,x3,x4))
      r (x1,(x2,x3,x4)) = (x1,x2,x3,x4)

instance Transparent Bool where
  describe = dimap l r $ proUnit +++ proUnit
    where
      l False = Left ()
      l True  = Right ()
      r (Left _)  = False
      r (Right _) = True

instance Transparent Ordering where
  describe = dimap l r $ proUnit +++ (proUnit +++ proUnit)
    where
      l LT = Left ()
      l EQ = Right (Left ())
      l GT = Right (Right ())
      
      r (Left _) = LT
      r (Right (Left _)) = EQ
      r (Right (Right _)) = GT

instance Transparent x => Transparent (Maybe x) where
  describe = dimap l r $ proUnit +++ describe
    where
      l = maybe (Left ()) Right
      r = either (const Nothing) Just

instance Transparent x => Transparent [x] where
  describe = go 
    where
      go = dimap l r $ proUnit +++ (describe *** go)
      
      l [] = Left ()
      l (x:xs) = Right (x,xs)

      r (Left _) = []
      r (Right (x,xs)) = x:xs
