{-# LANGUAGE BangPatterns #-}
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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}

module ModelFinder.Examples.Monad(
  M(..), I(..),
  MonadSig(..), (:->)(..),
  searchMonad
) where

import Control.Monad (guard)
import Data.Constraint.Extras
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.GADT.Compare
import Data.GADT.Show (GShow (..))
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Type.Equality
import ModelFinder.Solver
import Data.Finitary
import GHC.Generics (Generic)
import GHC.TypeNats (natVal)
import Data.Functor.Classes (showsUnaryWith)
import Data.Bifunctor (Bifunctor(..))

import ModelFinder.Expr

data I = I0 | I1
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass Finitary

data M = M0 | M1
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass Finitary

{- | Signature of data describing Monad on @T a = (M, I -> a)@

Let @T a@ be a functor of the following shape.

> type T a = (M, I -> a)

Any Monad on type can be written as follows:

> pure :: a -> T a
> pure a = (unit, const a)
> 
> join :: T (T a) -> T a
> join (m, f) = (munge m v, \i -> v (index1 m v i) (index2 m v i))
>   where v = fst . f
>         h = snd . f

using these unknown values and functions.

> unit :: M
> munge :: M -> (I -> M) -> M
> index1 :: M -> (I -> M) -> I -> I
> index2 :: M -> (I -> M) -> I -> I

By translating the Monad laws written in terms of @(pure, join)@ to
that of @(unit, munge, index1, index2)@, we can make equational theory
of Monads on T.

@MonadSig@ is the signature of terms, and equations are implemented afterwards.

-}
data MonadSig x where
  Unit :: MonadSig M
  Munge :: M -> (I :-> M) -> MonadSig M
  Index1 :: M -> (I :-> M) -> I -> MonadSig I
  Index2 :: M -> (I :-> M) -> I -> MonadSig I

-- * Monad Laws in terms of @MonadSig@

type Prop = Property MonadSig

unit :: Expr MonadSig M
unit = call Unit

munge :: Expr MonadSig M -> Expr MonadSig (I :-> M) -> Expr MonadSig M
munge = lift2 Munge

index1, index2 :: Expr MonadSig M -> Expr MonadSig (I :-> M) -> Expr MonadSig I -> Expr MonadSig I
index1 = lift3 Index1
index2 = lift3 Index2

constFn :: Expr MonadSig M -> Expr MonadSig (I :-> M)
constFn em = Fn . const <$> em

fn :: (I -> Expr MonadSig a) -> Expr MonadSig (I :-> a)
fn f = sequenceA (Fn f)

monadLaw1 :: M -> Prop
monadLaw1 m = munge (pure m) (constFn unit) `evaluatesTo` m

monadLaw2 :: M -> Prop
monadLaw2 m = munge unit (constFn (pure m)) `evaluatesTo` m

monadLaw3 :: M -> (I :-> M) -> ((I, I) :-> M) -> Prop
monadLaw3 m v w =
  let w' = fmap (w $$) <$> indexBoth m v
  in munge (munge (pure m) (pure v)) w' === munge (pure m) (mungeInner v w)

monadLaw4 :: M -> I -> Prop
monadLaw4 m i = index1 (pure m) (constFn unit) (pure i) `evaluatesTo` i

monadLaw5 :: M -> I -> Prop
monadLaw5 m i = index2 unit (constFn (pure m)) (pure i) `evaluatesTo` i

monadLaw678 :: M -> (I :-> M) -> ((I,I) :-> M) -> I -> (Prop, Prop, Prop)
monadLaw678 m v w i = (law6, law7, law8)
  where
    u = mungeInner v w
    w' = fmap (w $$) <$> indexBoth m v
    vw i' = (v $$ i', Fn $ \j -> w $$ (i',j))

    i1 = index1 (munge (pure m) (pure v)) w' (pure i)
    i2 = index2 (munge (pure m) (pure v)) w' (pure i)
    
    i1' = index1 (pure m) u (pure i)
    i2' = index2 (pure m) u (pure i)
    
    law6 = index1 (pure m) (pure v) i1 === i1'
    law7 = index2 (pure m) (pure v) i1 === index1' (vw <$> i1') i2'
    law8 = i2 === index2' (vw <$> i1') i2'

-- Aux functions to write laws

mungeInner :: (I :-> M) -> ((I, I) :-> M) -> Expr MonadSig (I :-> M)
mungeInner v w = fn $ \i -> munge (pure (v $$ i)) (pure $ Fn $ \j -> w $$ (i,j))

indexBoth :: M -> (I :-> M) -> Expr MonadSig (I :-> (I, I))
indexBoth m v = fn $ \i -> liftA2 (,) (index1 (pure m) (pure v) (pure i)) (index2 (pure m) (pure v) (pure i))

index1', index2' :: Expr MonadSig (M, I :-> M) -> Expr MonadSig I -> Expr MonadSig I
index1' = lift2 (\(m,v) i -> Index1 m v i)
index2' = lift2 (\(m,v) i -> Index2 m v i)

-- * Model definitions

-- >>> length $ searchMonad ()
-- *** Exception: ProgressCancelledException
searchMonad :: () -> [Solution MonadSig]
searchMonad _ = initialMonadModels >>= \model -> solve 10 model equations >>= constraintToSolution
  where
    ms = inhabitants :: [M]
    is = inhabitants :: [I]
    vs = allFunctions :: [I :-> M]
    ws = allFunctions :: [(I,I) :-> M]

    equations = Map.fromList $ zip [0 :: Int ..] (concat [law3eqs, law678eqs])

    law3eqs = monadLaw3 <$> ms <*> vs <*> ws
    law678eqs = do
      m <- ms
      v <- vs
      w <- ws
      i <- is
      let (p6,p7,p8) = monadLaw678 m v w i
      [p6, p7, p8]

-- | Law1,2,4,5 are "easy" laws, picking one exact value
--   for unknown functions at specific values.
--
-- >>> length initialMonadModels
-- 1
initialMonadModels :: [Model MonadSig]
initialMonadModels = solve 10 initialModel equations
  where
    ms = inhabitants :: [M]
    is = inhabitants :: [I]
    vs = allFunctions :: [I :-> M]
    
    allMs = Set.fromList ms
    allIs = Set.fromList is
    
    initialModel = Model $ DMap.fromList $
      [ Unit :=> Set.singleton M0 ] ++
      [ mungeSig :=> allMs | mungeSig <- Munge <$> ms <*> vs ] ++
      [ ix1Sig :=> allIs | ix1Sig <- Index1 <$> ms <*> vs <*> is ] ++
      [ ix2Sig :=> allIs | ix2Sig <- Index2 <$> ms <*> vs <*> is ]

    equations = Map.fromList $ zip [0 :: Int ..] (concat [law1eqs, law2eqs, law4eqs, law5eqs])

    law1eqs = monadLaw1 <$> ms
    law2eqs = monadLaw2 <$> ms
    law4eqs = monadLaw4 <$> ms <*> is
    law5eqs = monadLaw5 <$> ms <*> is

-------------------
-- Instances
-------------------

deriving instance Show (MonadSig x)
deriving instance Eq (MonadSig x)
deriving instance Ord (MonadSig x)

instance GShow MonadSig where gshowsPrec = showsPrec

instance GEq MonadSig where
  geq Unit Unit = Just Refl
  geq x@Munge{} y@Munge{} = guard (x == y) *> Just Refl
  geq x@Index1{} y@Index1{} = guard (x == y) *> Just Refl
  geq x@Index2{} y@Index2{} = guard (x == y) *> Just Refl
  geq _ _ = Nothing

instance GCompare MonadSig where
  gcompare Unit Unit = GEQ
  gcompare x@Munge{} y@Munge{} = monocompare x y
  gcompare x@Index1{} y@Index1{} = monocompare x y
  gcompare x@Index2{} y@Index2{} = monocompare x y

  gcompare Unit _ = GLT
  gcompare Munge{} Index1{} = GLT
  gcompare Munge{} Index2{} = GLT
  gcompare Index1{} Index2{} = GLT

  gcompare Munge{} Unit = GGT
  gcompare Index1{} Unit = GGT
  gcompare Index1{} Munge{} = GGT
  gcompare Index2{} _ = GGT


monocompare :: Ord (t a) => t a -> t a -> GOrdering a a
monocompare x y = case compare x y of
  LT -> GLT
  EQ -> GEQ
  GT -> GGT

instance (c I, c M) => Has c MonadSig where
  has sig body = case sig of
    Unit -> body
    Munge{} -> body
    Index1{} -> body
    Index2{} -> body

-----------------------
-- * Utilities
-----------------------

-- | Function with finite domain can be treated as data
--   (compare two functions, show to text, ...)
newtype (a :-> b) = Fn { ($$) :: a -> b }
  deriving Functor

instance (Finitary a, Eq b) => Eq (a :-> b) where
  Fn f == Fn g = all (\x -> f x == g x) inhabitants 

instance (Finitary a, Ord b) => Ord (a :-> b) where
  compare (Fn f) (Fn g) = foldMap (\x -> f x `compare` g x) inhabitants

instance (Finitary a, Show a, Show b) => Show (a :-> b) where
  showsPrec p f = showsUnaryWith showsPrec "makeFn" p (graph f)

instance (Finitary a) => Foldable ((:->) a) where
  foldMap g (Fn f) = foldMap (g . f) inhabitants

instance (Finitary a) => Traversable ((:->) a) where
  traverse g f = makeFn <$> traverse (traverse g) (graph f)

makeFn :: forall a b. (Finitary a) => [(a,b)] -> a :-> b
makeFn fnData
  | isTotalMap = Fn $ (m Map.!) . toFinite
  | otherwise = error "Not a data of total map"
  where
    m = Map.fromList (first toFinite <$> fnData)
    isTotalMap = toInteger (Map.size m) == toInteger (natVal @(Cardinality a) undefined)

graph :: (Finitary a) => (a :-> b) -> [(a,b)]
graph (Fn f) = (\a -> (a, f a)) <$> inhabitants

allFunctions :: (Ord a, Finitary a, Finitary b) => [a :-> b]
allFunctions = makeFn <$> traverse (\a -> (,) a <$> inhabitants) inhabitants
