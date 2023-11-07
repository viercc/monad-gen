{-# LANGUAGE RankNTypes #-}
module Data.Profunctor.Power where

import Data.Profunctor
import Data.Profunctor.Cartesian
import Data.Void (absurd)
import Data.Transparent

newtype Power p a b = Power { runPower :: forall s t. p s t -> p (b -> s) (a -> t) }

instance Profunctor p => Profunctor (Power p) where
    dimap f g (Power k) = Power (dimap (. g) (. f) . k)

instance Profunctor p => Cartesian (Power p) where
    proUnit = Power $ dimap ($ ()) const
    ep *** eq = Power $ \e -> dimap curry uncurry $ runPower ep (runPower eq e)

instance Cartesian p => Cocartesian (Power p) where
    proEmpty = Power $ \_ -> dimap id (const absurd) proUnit
    ep +++ eq = Power $ \e -> dimap (\f -> (f . Left, f . Right)) (uncurry either) $ runPower ep e *** runPower eq e

ptraverseFunction :: forall x p a b. (Transparent x, Cartesian p) => p a b -> p (x -> a) (x -> b)
ptraverseFunction = runPower describe