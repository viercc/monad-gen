{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module ModelFinder.Dependent.Examples.Monad(
  M(..), I(..), V2(..),
  MonadSig(..),
  searchMonad,
  orMonoid, xorMonoid
) where

import Control.Monad (guard)
import Data.Constraint.Extras
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.GADT.Compare
import Data.GADT.Show (GShow (..))
import Data.Set qualified as Set
import Data.Type.Equality

import ModelFinder.Dependent.Solver
import ModelFinder.Dependent.Expr

data I = I0 | I1
  deriving stock (Show, Eq, Ord, Enum, Bounded)

data M = M0 | M1
  deriving stock (Show, Eq, Ord, Enum, Bounded)

-- | V2 a ~ (I -> a)
data V2 a = V2 !a !a
  deriving stock (Show, Eq, Ord, Functor)

enumV2 :: [a] -> [V2 a]
enumV2 as = V2 <$> as <*> as

(!) :: V2 a -> I -> a
V2 a0 a1 ! i = case i of
  I0 -> a0
  I1 -> a1

{- | Signature of data describing Monad on @T a = (M, I -> a)@

Let @T a@ be a functor of the following shape.

> type T a = (M, I -> a)

Any Monad on type can be written as follows:

> pure :: a -> T a
> pure a = (unit, const a)
> 
> join :: T (T a) -> T a
> join (m, f) = (bull m v, \i -> v (ixL m v i) (ixR m v i))
>   where v = fst . f
>         h = snd . f

using these unknown values and functions.

> unit :: M
> bull :: M -> (I -> M) -> M
> ixL :: M -> (I -> M) -> I -> I
> ixR :: M -> (I -> M) -> I -> I

By translating the Monad laws written in terms of @(pure, join)@ to
that of @(unit, bull, ixL, ixR)@, we can make equational theory
of Monads on T.

@MonadSig@ is the signature of terms, and equations are implemented afterwards.

-}
data MonadSig x where
  Unit :: MonadSig M
  Bull :: !M -> !(V2 M) -> MonadSig M
  L :: !M -> !(V2 M) -> !I -> MonadSig I
  R :: !M -> !(V2 M) -> !I -> MonadSig I

-- * Monad Laws in terms of @MonadSig@

type Prop = Property MonadSig

unit :: Expr MonadSig M
unit = call Unit

bull :: Expr MonadSig M -> Expr MonadSig (V2 M) -> Expr MonadSig M
bull = lift2 Bull

ixL, ixR :: Expr MonadSig M -> Expr MonadSig (V2 M) -> Expr MonadSig I -> Expr MonadSig I
ixL = lift3 L
ixR = lift3 R

constFn :: Expr MonadSig M -> Expr MonadSig (V2 M)
constFn em = (\m -> V2 m m) <$> em

fn :: (I -> Expr MonadSig a) -> Expr MonadSig (V2 a)
fn f = V2 <$> f I0 <*> f I1

monadLaw1 :: M -> Prop
monadLaw1 m = bull (pure m) (constFn unit) `evaluatesTo` m

monadLaw2 :: M -> Prop
monadLaw2 m = bull unit (constFn (pure m)) `evaluatesTo` m

monadLaw3 :: M -> V2 M -> V2 (V2 M) -> Prop
monadLaw3 m v w =
  bull (bull (pure m) (pure v)) (delta m v w) === bull (pure m) (bullInner v w)

monadLaw4 :: M -> I -> Prop
monadLaw4 m i = ixL (pure m) (constFn unit) (pure i) `evaluatesTo` i

monadLaw5 :: M -> I -> Prop
monadLaw5 m i = ixR unit (constFn (pure m)) (pure i) `evaluatesTo` i

monadLaw678 :: M -> V2 M -> V2 (V2 M) -> I -> (Prop, Prop, Prop)
monadLaw678 m v w i = (law6, law7, law8)
  where
    u = bullInner v w
    w' = delta m v w
    vw k = (v ! k, w ! k)

    i1 = ixL (bull (pure m) (pure v)) w' (pure i)
    i2 = ixR (bull (pure m) (pure v)) w' (pure i)
    
    i1' = ixL (pure m) u (pure i)
    i2' = ixR (pure m) u (pure i)
    
    law6 = ixL (pure m) (pure v) i1 === i1'
    law7 = ixR (pure m) (pure v) i1 === ixL' (vw <$> i1') i2'
    law8 = i2 === ixR' (vw <$> i1') i2'

-- Aux functions to write laws

bullInner :: V2 M -> V2 (V2 M) -> Expr MonadSig (V2 M)
bullInner v w = fn $ \i -> call $ Bull (v ! i) (w ! i)

delta :: M -> V2 M -> V2 (V2 M) -> Expr MonadSig (V2 M)
delta m v w = fn $ \i -> liftA2 (\j k -> w ! j ! k) (ixL (pure m) (pure v) (pure i)) (ixR (pure m) (pure v) (pure i))

ixL', ixR' :: Expr MonadSig (M, V2 M) -> Expr MonadSig I -> Expr MonadSig I
ixL' = lift2 (\(m,v) i -> L m v i)
ixR' = lift2 (\(m,v) i -> R m v i)

-- * Model definitions

initialModel :: Model MonadSig
initialModel = Model $ DMap.fromList $
  [ Unit :=> allMs ] ++
  [ bullSig :=> allMs | bullSig <- Bull <$> ms <*> vs ] ++
  [ ix1Sig :=> allIs | ix1Sig <- L <$> ms <*> vs <*> is ] ++
  [ ix2Sig :=> allIs | ix2Sig <- R <$> ms <*> vs <*> is ]
  where
    ms = inhabitants :: [M]
    is = inhabitants :: [I]
    vs = enumV2 ms :: [V2 M]
    
    allMs = Set.fromList ms
    allIs = Set.fromList is

-- >>> IntMap.size monadLaws1245
-- 13
monadLaws1245 :: [Property MonadSig]
monadLaws1245 = concat [law1eqs, law2eqs, law4eqs, law5eqs]
  where
    ms = inhabitants :: [M]
    is = inhabitants :: [I]

    law1eqs = monadLaw1 <$> ms
    law2eqs = monadLaw2 <$> ms
    law4eqs = monadLaw4 <$> ms <*> is
    law5eqs = monadLaw5 <$> ms <*> is

-- >>> IntMap.size monadLaws3678
-- 896
monadLaws3678 :: [Property MonadSig]
monadLaws3678 = law3eqs ++ law678eqs
  where
    ms = inhabitants :: [M]
    is = inhabitants :: [I]
    vs = enumV2 ms :: [V2 M]
    ws = enumV2 vs :: [V2 (V2 M)]

    law3eqs = monadLaw3 <$> ms <*> vs <*> ws
    law678eqs = do
      m <- ms
      v <- vs
      w <- ws
      i <- is
      let (p6,p7,p8) = monadLaw678 m v w i
      [p6, p7, p8]

eqsFromMonoid :: M -> (M -> M -> M) -> [Property MonadSig]
eqsFromMonoid e op = unitDef : monoidDefs
  where
    ms = inhabitants :: [M]

    unitDef = pure $ PropDef Unit e
    monoidDefs = do
      x <- ms
      y <- ms
      pure $ bull (pure x) (pure (V2 y y)) `evaluatesTo` op x y

xorMonoid :: M -> M -> M
xorMonoid = op
  where
    op M0 y = y
    op x  M0 = x
    op M1 M1 = M0

orMonoid :: M -> M -> M
orMonoid = op
  where
    op M0 y = y
    op x  M0 = x
    op M1 M1 = M1

-- >>> length $ searchMonad M0 xorMonoid
-- 4
-- >>> length $ searchMonad M0 orMonoid
-- 8
searchMonad :: M -> (M -> M -> M) -> [Model MonadSig]
searchMonad e op = initialMonadModels e op >>= \model -> solve model monadLaws3678

-- | Law1,2,4,5 are "easy" laws, picking one exact value
--   for unknown functions at specific values.
--
-- >>> length $ initialMonadModels M0 xorMonoid
-- 1
-- >>> length $ initialMonadModels M0 orMonoid
-- 1
initialMonadModels :: M -> (M -> M -> M) -> [Model MonadSig]
initialMonadModels e op = solve initialModel (eqsFromMonoid e op ++ monadLaws1245)

-------------------
-- Instances
-------------------

deriving instance Show (MonadSig x)
deriving instance Eq (MonadSig x)
deriving instance Ord (MonadSig x)

instance GShow MonadSig where gshowsPrec = showsPrec

instance GEq MonadSig where
  geq Unit Unit = Just Refl
  geq x@Bull{} y@Bull{} = guard (x == y) *> Just Refl
  geq x@L{} y@L{} = guard (x == y) *> Just Refl
  geq x@R{} y@R{} = guard (x == y) *> Just Refl
  geq _ _ = Nothing

instance GCompare MonadSig where
  gcompare Unit Unit = GEQ
  gcompare x@Bull{} y@Bull{} = monocompare x y
  gcompare x@L{} y@L{} = monocompare x y
  gcompare x@R{} y@R{} = monocompare x y

  gcompare Unit _ = GLT
  gcompare Bull{} L{} = GLT
  gcompare Bull{} R{} = GLT
  gcompare L{} R{} = GLT

  gcompare Bull{} Unit = GGT
  gcompare L{} Unit = GGT
  gcompare L{} Bull{} = GGT
  gcompare R{} _ = GGT

monocompare :: Ord (t a) => t a -> t a -> GOrdering a a
monocompare x y = case compare x y of
  LT -> GLT
  EQ -> GEQ
  GT -> GGT

instance (c I, c M) => Has c MonadSig where
  has sig body = case sig of
    Unit -> body
    Bull{} -> body
    L{} -> body
    R{} -> body

---- Utility

inhabitants :: (Enum x, Bounded x) => [x]
inhabitants = [minBound ..]
