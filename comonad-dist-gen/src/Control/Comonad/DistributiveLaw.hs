{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Control.Comonad.DistributiveLaw(
  Dist,
  Equals(..),
  law1, law2, law3, law4
) where

import Control.Comonad

-- | Distributive law
type Dist w v = forall x. w (v x) -> v (w x)

-- | Type of "equation" on a
data Equals a = Equals { lhs :: a, rhs :: a }
  deriving Functor

infix 2 ====
(====) :: a -> a -> Equals a
(====) = Equals

-- Distributive law laws

law1 :: (Comonad w, Comonad v) => Dist w v -> Equals (forall x. w (v x) -> w x)
law1 dist = extract . dist ==== fmap extract

law2 :: (Comonad w, Comonad v) => Dist w v -> Equals (forall x. w (v x) -> v x)
law2 dist = fmap extract . dist ==== extract

law3 :: (Comonad w, Comonad v) => Dist w v -> Equals (forall x. w (v x) -> v (v (w x)))
law3 dist = duplicate . dist ==== fmap dist . dist . fmap duplicate

law4 :: (Comonad w, Comonad v) => Dist w v -> Equals (forall x. w (v x) -> v (w (w x)))
law4 dist = fmap duplicate . dist ==== dist . fmap dist . duplicate
