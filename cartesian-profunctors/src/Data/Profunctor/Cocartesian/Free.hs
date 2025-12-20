{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Profunctor.Cocartesian.Free(
    -- * The free 'Cocartesian' profunctors
    FreeCocartesian(..),
    liftF, foldFree,
    emptyF, sumF,

    -- ** Distributive 'Cartesian' on @FreeCocartesian p@
    multF,

    -- * Newtype wrapper
    ForgetCocartesian(..),

    -- * Utility functions handling product @(,)@ and coproduct @Either@ of
    --   Haskell types

    assocEither, unassocEither,
    distL, undistL,
    distR, undistR
) where

import Data.Void (Void, absurd)
import Data.Profunctor (Profunctor(..), (:->))
import Data.Profunctor.Cartesian
import Data.Bifunctor (Bifunctor(..))
import Data.Profunctor.Monad
import Data.Profunctor.Day

-- * Free Cocartesian

-- | Free Cocartesian profunctor is 'FreeMonoidal' profunctor with respect to
--   @Either@.
-- 
-- ==== Caution about 'Cartesian' instance
-- 
-- Note that @'FreeCocartesian' p@ have an instance of 'Cartesian', by distributing
-- product on sums to sum of products of individual profunctors.
-- When it is desirable to disable @Cartesian@ instance of @FreeCocartesian p@,
-- use 'Data.Profunctor.Cartesian.Free.ForgetCartesian' to ignore @Cartesian@ instance of @p@.
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
data FreeCocartesian p a b =
    Neutral (a -> Void)
  | Cons (Day Either p (FreeCocartesian p) a b)
  deriving Functor

instance Cartesian p => Applicative (FreeCocartesian p a) where
  pure = pureDefault
  liftA2 = liftA2Default

instance Profunctor (FreeCocartesian p) where
    dimap f g fp = case fp of
        Neutral a -> Neutral (a . f)
        Cons ps' -> Cons (dimap f g ps')

instance ProfunctorFunctor FreeCocartesian where
  promap pq ps = case ps of
    Neutral a -> Neutral a
    Cons (Day p ps' opA opB) -> Cons $ Day (pq p) (promap pq ps') opA opB

emptyF :: FreeCocartesian p Void b
emptyF = Neutral id

sumF :: FreeCocartesian p a b -> FreeCocartesian p a' b' -> FreeCocartesian p (Either a a') (Either b b')
sumF ps qs = case ps of
  Neutral z -> dimap (either (absurd . z) id) Right qs
  Cons (Day p ps' opA opB) ->
    Cons $ Day p (sumF ps' qs) (assocEither . first opA) (first opB . unassocEither)

assocEither :: Either (Either a b) c -> Either a (Either b c)
assocEither = either (second Left) (Right . Right)

unassocEither :: Either a (Either b c) -> Either (Either a b) c
unassocEither = either (Left . Left) (first Right)

instance Profunctor p => Cocartesian (FreeCocartesian p) where
    proEmpty = emptyF
    (+++) = sumF

instance Cartesian p => Cartesian (FreeCocartesian p) where
    proUnit = liftF proUnit
    (***) = multF (***)

type ProductOp p q r = forall a1 b1 a2 b2. p a1 b1 -> q a2 b2 -> r (a1,a2) (b1,b2)

multF :: ProductOp p q r -> FreeCocartesian p a b -> FreeCocartesian q a' b' -> FreeCocartesian r (a,a') (b,b')
multF _    (Neutral z) _ = lmap (z . fst) emptyF
multF prod (Cons (Day p ps' opA opB)) qs
  = dimap (distR . first opA) (first opB . undistR) $
      sumF (distLeftFree prod p qs) (multF prod ps' qs)

distLeftFree :: ProductOp p q r -> p a b -> FreeCocartesian q a' b' -> FreeCocartesian r (a,a') (b,b')
distLeftFree _    _ (Neutral z) = lmap (z . snd) emptyF
distLeftFree prod p (Cons (Day q qs' opA opB)) = Cons $ Day (prod p q) (distLeftFree prod p qs') (distL . second opA) (second opB . undistL)

distR :: (Either a1 a2, b) -> Either (a1, b) (a2, b)
distR (ea, b) = bimap (, b) (, b) ea

undistR :: Either (a1, b) (a2, b) -> (Either a1 a2, b)
undistR = either (first Left) (first Right)

distL :: (a, Either b1 b2) -> Either (a, b1) (a, b2)
distL (a,b) = bimap (a,) (a,) b

undistL :: Either (a, b1) (a, b2) -> (a, Either b1 b2)
undistL = either (second Left) (second Right)

-- * ProfunctorMonad structures

liftF :: p :-> FreeCocartesian p
liftF p = Cons $ Day p emptyF Left (either id absurd)

foldFree :: (Cocartesian q) => (p :-> q) -> FreeCocartesian p :-> q
foldFree handle ps = case ps of
    Neutral z -> lmap z proEmpty
    Cons (Day p ps' opA opB) -> dimap opA opB (handle p +++ foldFree handle ps')

instance ProfunctorMonad FreeCocartesian where
    proreturn = liftF
    projoin = foldFree id

-- * Utility newtype wrappers

-- | Forgets 'Cocartesian' instance from a 'Profunctor'.
newtype ForgetCocartesian p a b = ForgetCocartesian { recallCocartesian :: p a b }
  deriving newtype (Functor, Profunctor, Cartesian)
  -- DO NOT add "deriving Cocartesian" clause!
