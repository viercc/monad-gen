{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
module Data.Profunctor.Cartesian.Free(
    FreeMonoidal(..),

    FreeCartesian,
    liftFreeCartesian,
    foldFreeCartesian,

    FreeCocartesian,
    liftFreeCocartesian,
    foldFreeCocartesian,

    ForgetCartesian(..),
    ForgetCocartesian(..)
) where

import Data.Void (Void, absurd)
import Data.Profunctor (Profunctor(..), (:->))
import Data.Profunctor.Cartesian
import Data.Bifunctor (Bifunctor(..))
import Data.Profunctor.Monad
import Data.Profunctor.Day

-- * Free monoidal profunctor

-- | Constructs free monoidal profunctor with specified monoid. Each parameters of @FreeMonoidal t i p@ stands for:
--
-- - @t@ for the monoidal product
-- - @i@ for the unit of the monoidal product @t@
-- - @p@ for the profunctor generating @FreeMonoidal@
-- 
-- For example, @FreeMonoidal (,) () p@ is the free 'Cartesian' profunctor.
data FreeMonoidal t i p a b =
    Neutral (a -> i) (i -> b)
  | Cons (Day t p (FreeMonoidal t i p) a b)

deriving instance Functor (FreeMonoidal t i p a)


instance Profunctor (FreeMonoidal t i p) where
    dimap f g fp = case fp of
        Neutral a b -> Neutral (a . f) (g . b)
        Cons ps' -> Cons (dimap f g ps')

instance ProfunctorFunctor (FreeMonoidal t i) where
  promap pq ps = case ps of
    Neutral a b -> Neutral a b
    Cons (Day p ps' opA opB) -> Cons $ Day (pq p) (promap pq ps') opA opB

-- * Free Cartesian

-- | Free Cartesian profunctor is 'FreeMonoidal' profunctor with respect to
--   @(,)@.
type FreeCartesian = FreeMonoidal (,) ()

instance Cartesian (FreeCartesian p) where
    proUnit = Neutral (const ()) id
    Neutral _ b *** qs = dimap snd (b (),) qs
    Cons (Day p ps opA opB) *** qs = Cons $ Day p (ps *** qs) (assocTup . first opA) (first opB . unassocTup)

assocTup :: ((a,b), c) -> (a, (b,c))
assocTup ((a,b), c) = (a, (b,c))

unassocTup :: (a, (b,c)) ->  ((a,b), c)
unassocTup (a, (b,c)) = ((a,b), c)

liftFreeCartesian :: p :-> FreeCartesian p
liftFreeCartesian p = Cons $ Day p proUnit (, ()) fst

foldFreeCartesian :: Cartesian q => (p :-> q) -> FreeCartesian p :-> q
foldFreeCartesian _ (Neutral _ b) = rmap b proUnit
foldFreeCartesian handle (Cons ps) = prodDay handle (foldFreeCartesian handle) ps

instance ProfunctorMonad FreeCartesian where
  proreturn = liftFreeCartesian
  projoin = foldFreeCartesian id

-- * Free Cocartesian profunctor


-- | Free Cocartesian profunctor is 'FreeMonoidal' profunctor with respect to
--   @Either@.
-- 
-- ==== Caution about 'Cartesian' instance
-- 
-- Note that @'FreeCocartesian' p@ have an instance of 'Cartesian', by distributing
-- product on sums to sum of products of individual profunctors.
-- When it is desirable to disable @Cartesian@ instance of @FreeCocartesian p@,
-- use 'ForgetCartesian' to ignore @Cartesian@ instance of @p@.
--
-- Because there are some profunctors which are both @Cartesian@ and @Cocartesian@
-- but do not satisfy distributive laws,
-- using 'FreeCocartesian' with such profunctors might cause a surprising behavior.
--
-- For example, @'Data.Bifunctor.Joker.Joker' []@ is not distributive,
-- as @Alternative []@ is not distributive as shown below.
-- 
-- >>> import Control.Applicative
-- >>> let x = [id, id]
-- >>> let y = [1]; z = [2]
-- >>> x <*> (y <|> z)
-- [1,2,1,2]
-- >>> (x <*> y) <|> (x <*> z)
-- [1,1,2,2]
-- 
-- With such non-distributive @Cartesian p@, 'foldFreeCocartesian' does not preserve
-- the @Cartesian@ operations. The following equation does not have to hold.
--
-- @
-- -- Not necessarily holds!
-- foldFreeCocartesian id (ps *** qs)
--  == foldFreeCocartesian id ps *** foldFreeCocartesian id qs
-- @
-- 
type FreeCocartesian = FreeMonoidal Either Void

instance Profunctor p => Cocartesian (FreeCocartesian p) where
    proEmpty = Neutral id absurd
    Neutral z _ +++ qs = dimap (either (absurd . z) id) Right qs
    Cons (Day p ps' opA opB) +++ qs = Cons $ Day p (ps' +++ qs) (assocEither . first opA) (first opB . unassocEither)

instance Cartesian p => Cartesian (FreeCocartesian p) where
    proUnit = liftFreeCocartesian proUnit
    (***) = multCocartesian

assocEither :: Either (Either a b) c -> Either a (Either b c)
assocEither = either (second Left) (Right . Right)

unassocEither :: Either a (Either b c) -> Either (Either a b) c
unassocEither = either (Left . Left) (first Right)

liftFreeCocartesian :: p :-> FreeCocartesian p
liftFreeCocartesian p = Cons $ Day p (Neutral id absurd) Left (either id absurd)

foldFreeCocartesian :: (Cocartesian q) => (p :-> q) -> FreeCocartesian p :-> q
foldFreeCocartesian handle ps = case ps of
    Neutral z _ -> lmap z proEmpty
    Cons (Day p ps' opA opB) -> dimap opA opB (handle p +++ foldFreeCocartesian handle ps')

distLeftFree :: Cartesian p => p a b -> FreeCocartesian p a' b' -> FreeCocartesian p (a,a') (b,b')
distLeftFree _ (Neutral z _) = lmap (z . snd) proEmpty
distLeftFree p (Cons (Day q qs' opA opB)) = Cons $ Day (p *** q) (distLeftFree p qs') (distL . second opA) (second opB . undistL)

distR :: (Either a1 a2, b) -> Either (a1, b) (a2, b)
distR (ea, b) = bimap (, b) (, b) ea

undistR :: Either (a1, b) (a2, b) -> (Either a1 a2, b)
undistR = either (first Left) (first Right)

distL :: (a, Either b1 b2) -> Either (a, b1) (a, b2)
distL (a,b) = bimap (a,) (a,) b

undistL :: Either (a, b1) (a, b2) -> (a, Either b1 b2)
undistL = either (second Left) (second Right)

multCocartesian :: Cartesian p => FreeCocartesian p a b -> FreeCocartesian p a' b' -> FreeCocartesian p (a,a') (b,b')
multCocartesian (Neutral z _) _ = lmap (z . fst) proEmpty
multCocartesian (Cons (Day p ps' opA opB)) qs = dimap (distR . first opA) (first opB . undistR) $ distLeftFree p qs +++ (ps' *** qs)

instance ProfunctorMonad FreeCocartesian where
    proreturn = liftFreeCocartesian
    projoin = foldFreeCocartesian id

-- | Forgets 'Cartesian' instance from a 'Profunctor'.
newtype ForgetCartesian p a b = ForgetCartesian { recallCartesian :: p a b }
  deriving newtype (Functor, Profunctor, Cocartesian)
  -- DO NOT add "deriving Cartesian" clause!

-- | Forgets 'Cocartesian' instance from a 'Profunctor'.
newtype ForgetCocartesian p a b = ForgetCocartesian { recallCocartesian :: p a b }
  deriving newtype (Functor, Profunctor, Cartesian)
  -- DO NOT add "deriving Cocartesian" clause!
