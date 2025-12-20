{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeAbstractions #-}

module Data.PTraversable.Internal.Day (ptraverseDay) where

import Prelude hiding (Enum)
import Data.Profunctor.Cocartesian.Free

import Data.Profunctor
import Data.Profunctor.Cartesian

import Data.Functor.Day ( Day(..) )
import Control.Monad.Trans.State.Lazy (State, state, evalState)

import qualified Data.Vector as V
import Data.Bifunctor (Bifunctor(..))
import GHC.TypeNats
import Data.Finite (Finite, getFinite, finite)
import Data.Monoid (Endo(..))

type Optic p s t a b = p a b -> p s t
type Traversal s t a b = forall p. (Cartesian p, Cocartesian p) => Optic p s t a b

-- An "instance" of (PTraversable t). They are used instead of constraint (PTraversable t),
-- because this module can't depend on Data.PTraversable module to avoid circular import.
type PT t = forall a b. Traversal (t a) (t b) a b

-- Explicit versions of superclasses of Traversal
traverseWith :: (Applicative f) => PT t -> (a -> f b) -> t a -> f (t b)
traverseWith travT f = runStar (travT (Star f))

fmapWith :: PT t -> (a -> b) -> t a -> t b
fmapWith = id

foldrWith :: PT t -> (a -> r -> r) -> r -> t a -> r
foldrWith travT f z ta = ($ z) $ appEndo $ runForget (travT (Forget $ Endo . f)) ta

toListWith :: PT t -> t a -> [a]
toListWith travT = foldrWith travT (:) []

indices :: PT t -> t a -> t Int
indices travT ta = evalState (traverseWith travT indexStep ta) 0
  where
    indexStep :: x -> State Int Int
    indexStep _ = state $ \n -> n `seq` (n, succ n)

-- * Auxiliary definitions

-- Mono
data Mono a b = M b Natural

instance Profunctor Mono where
  dimap _ g (M b e) = M (g b) e

instance Cartesian Mono where
  proUnit = M () 0
  M b e *** M b' f = M (b, b') (e + f)

-- Polynomial is sum of monomials
type Poly = FreeCocartesian Mono

idPoly :: Poly () ()
idPoly = liftF (M () 1)

-- Adds context @s,t@ to a @Cocartesian p@.
newtype ContextT s t p a b = ContextT {
    unContextT :: p (a,s) (b,t)
  }

instance Profunctor p => Profunctor (ContextT s t p) where
  dimap f g = ContextT . dimap (first f) (first g) . unContextT

instance Cocartesian p => Cocartesian (ContextT s t p) where
  proEmpty = ContextT $ dimap fst id proEmpty
  ContextT p +++ ContextT q = ContextT $ dimap distR undistR (p +++ q)

-----------

type Day' t u x = ((t (), u ()), Int -> Int -> x)

ptraverseDay :: forall t u p a b.
     (Cartesian p, Cocartesian p)
  => PT t -> PT u
  -> p a b -> p (Day t u a) (Day t u b)
ptraverseDay travT travU p = dimap pre post travDay'
  where
    tShapes :: Poly (t ()) (t ())
    tShapes = travT idPoly

    uShapes :: Poly (u ()) (u ())
    uShapes = travU idPoly

    travDay' :: p (Day' t u a) (Day' t u b)
    travDay' = unContextT $ foldFree id (multF (interpretMonos p) tShapes uShapes)

    pre :: Day t u a -> Day' t u a
    pre (Day tb uc op) = ((t1, u1), op')
      where
        t1 = fmapWith travT (const ()) tb
        bs = V.fromList (toListWith travT tb)
        u1 = fmapWith travU (const ()) uc
        cs = V.fromList (toListWith travU uc)
        op' i j = op (bs V.! i) (cs V.! j)

    post :: Day' t u b -> Day t u b
    post ((t1, u1), op) = Day (indices travT t1) (indices travU u1) op

interpretMonos ::
  forall p a b s0 t0 s1 t1.
     (Cartesian p)
  => p a b
  -> Mono s0 t0 -> Mono s1 t1 -> ContextT (Int -> Int -> a) (Int -> Int -> b) p (s0, s1) (t0, t1)
interpretMonos p (M t0 m) (M t1 n)
  | m == 0 || n == 0 = ContextT $ rmap (const ((t0,t1), \_ _ -> error "should not reach here")) proUnit
  | otherwise = ContextT $ dimap pre post $ powPowerPartial p (m * n)
    where
      pre :: ((s0, s1), Int -> Int -> a) -> Natural -> a
      pre (_, op) i = case quotRem (fromIntegral i) (fromIntegral m) of
        (j,k) -> op j k
      
      post :: (Natural -> b) -> ((t0, t1), Int -> Int -> b)
      post f = ((t0, t1), \j k -> f (fromIntegral j * m + fromIntegral k))

powPowerPartial :: Cartesian p => p a b -> Natural -> p (Natural -> a) (Natural -> b)
powPowerPartial p n = case someNatVal n of
  SomeNat sn -> dimap (. fromInteger . getFinite) (. toFinite' sn) (proPower p)
  where
    toFinite' :: forall proxy n. KnownNat n => proxy n -> Natural -> Finite n
    toFinite' _ = finite . toInteger
