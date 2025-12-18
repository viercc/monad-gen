{-# LANGUAGE CPP #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeAbstractions #-}

module Data.PTraversable.Internal.Day (ptraverseDay) where

import Prelude hiding (Enum)
import Data.Profunctor.Cartesian.Free

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
idPoly = liftFreeCocartesian (M () 1)

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

interpretMono :: forall u p a b s' t'.
  (Cartesian p, Cocartesian p)
  => PT u -> p a b -> Mono s' t' -> ContextT (u (V.Vector a)) (u (V.Vector b)) p s' t'
interpretMono travU p (M t' n) = ContextT $ dimap snd (t', ) (travU powVector)
  where
    powVector :: p (V.Vector a) (V.Vector b)
    powVector = case someNatVal n of
      SomeNat sn -> dimap indexFinite (generateFinite sn) (proPower p)

    indexFinite :: V.Vector x -> Finite n -> x
    indexFinite xs i = xs V.! fromInteger (getFinite i)

    generateFinite :: forall proxy n x. KnownNat n => proxy n -> (Finite n -> x) -> V.Vector x
    generateFinite sn f = V.generate (fromIntegral (natVal sn)) (f . finite . toInteger)

ptraverseDay :: forall t u p a b.
     (Cartesian p, Cocartesian p)
  => PT t -> PT u
  -> p a b -> p (Day t u a) (Day t u b)
ptraverseDay travT travU p = dimap pre post travDay'
  where
    tShapes :: Poly (t ()) (t ())
    tShapes = travT idPoly

    travDay' :: p (t (), u (V.Vector a)) (t (), u (V.Vector b))
    travDay' = unContextT (foldFreeCocartesian (interpretMono travU p) tShapes)

    pre :: Day t u a -> (t (), u (V.Vector a))
    pre (Day tb uc op) = (t1, fmapWith travU (\c -> fmap (`op` c) bs) uc)
      where
        t1 = fmapWith travT (const ()) tb
        bs = V.fromList (toListWith travT tb)

    post :: (t (), u (V.Vector b)) -> Day t u b
    post (t1, ubs) = Day (indices travT t1) ubs (flip (V.!))
