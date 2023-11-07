{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.PTraversable.Internal.Day (ptraverseDay) where

import Data.Profunctor.Cartesian.Free
import Data.Void (absurd)
import Data.Profunctor.Power (ptraverseFunction)
import Data.Profunctor.FinFn (withFinFn)
import Data.Function ((&))

import Data.Profunctor
import Data.Profunctor.Cartesian
import Data.Transparent

import Data.Functor.Day ( Day(..) )
import Control.Monad.Trans.State.Lazy (State, state, runState)

type Optic p s t a b = p a b -> p s t
type Traversal s t a b = forall p. (Cartesian p, Cocartesian p) => Optic p s t a b

-- An "instance" of (PTraversable t). They are used instead of constraint (PTraversable t),
-- because this module can't depend on Data.PTraversable module to avoid circular import.
type PT t = forall a b. Traversal (t a) (t b) a b

data SomePower a b s t where
  SomePower :: (Transparent x) => (s -> (x -> a)) -> ((x -> b) -> t) -> SomePower a b s t

instance Profunctor (SomePower a b) where
  dimap f g (SomePower to from) = SomePower (to . f) (g . from)

instance Cartesian (SomePower a b) where
  proUnit = SomePower (const absurd) (const ())
  SomePower to from *** SomePower to' from' =
    SomePower (\(s,s') -> either (to s) (to' s')) (\k -> (from (k . Left), from' (k . Right)))

type SOP a b s t = FreeCocartesian (SomePower a b) s t

idPow :: SomePower a b a b
idPow = SomePower const ($ ())

idSOP :: SOP a b a b
idSOP = liftFreeCocartesian idPow

ptraverseDay :: forall t u p a b.
     (Cartesian p, Cocartesian p)
  => PT t -> PT u
  -> p a b -> p (Day t u a) (Day t u b)
ptraverseDay travT travU p = dimap (unwrapDay travT travU) wrapDay $ ptraverseDay' travT travU p

ptraverseDay' :: forall t u p a b.
     (Cartesian p, Cocartesian p)
  => PT t -> PT u
  -> p a b -> p (Day' t u a) (Day' t u b)
ptraverseDay' travT travU p = go (travT idSOP)
  where
    go :: forall s0 t0. SOP Int Int s0 t0 -> p (s0, u (Int -> a)) (t0, u (Int -> b))
    go (ProEmpty z) = lmap (z . fst) proEmpty
    go (ProSum (SomePower @x _ mkT) rest opA opB) = dimap pre post $ uFn +++ go rest
      where
        uFn = travU (ptraverseFunction @x p)
        (x2i, i2x) = embeddingToInt @x
        pre (s0, y) = case opA s0 of
          Left _ -> Left (travU (. x2i) y)
          Right a2 -> Right (a2, y)
        
        post (Left y) = (opB (Left (mkT x2i)), travU (. i2x) y)
        post (Right (b2,y)) = (opB (Right b2), y)

embeddingToInt :: forall x. Transparent x => (x -> Int, Int -> x)
embeddingToInt = withFinFn describe (\to from -> (fromIntegral . to, from . fromIntegral))

type Day' t u a = (t Int, u (Int -> a))

unwrapDay :: PT t -> PT u -> Day t u a -> Day' t u a
unwrapDay travT fmapU (Day tb uc op) = case separate travT tb of
  (ti, bs) -> (ti, fmapU (\c i -> op (bs !! i) c) uc)

wrapDay :: Day' t u a -> Day t u a
wrapDay (ti, uf) = Day ti uf (&)

separate :: PT t -> t a -> (t Int, [a])
separate travT ta =
  let mResult = runStar (travT indexStep) ta
      (ti, (xs, _)) = runState mResult (id, 0)
  in (ti, xs [])

indexStep :: Star (State ([x] -> [x], Int)) x Int
indexStep = Star $ \x -> state $ \(xs, n) -> (n, (xs . (x :), succ n))