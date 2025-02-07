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

module ModelFinder.Examples.Group(
  GroupSig(..),
  searchGroupOfOrder,
  prettyPrintSolution
) where

import Control.Monad (guard)
import Data.Constraint.Extras
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum (DSum (..))
import Data.Foldable (for_)
import Data.GADT.Compare
import Data.GADT.Show (GShow (..))
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Type.Equality
import ModelFinder

-- | Signature of functions which defines group structure on @a@.
data GroupSig a x where
  Ident :: GroupSig a a
  Inv :: a -> GroupSig a a
  Mul :: a -> a -> GroupSig a a

----

type GroupExpr a = Expr (GroupSig a) a

type GroupProp a = Expr (GroupSig a) Bool

gIdent :: GroupExpr a
gIdent = call Ident

gInv :: GroupExpr a -> GroupExpr a
gInv mx = mx >>= \x -> call (Inv x)

(|*|) :: GroupExpr a -> GroupExpr a -> GroupExpr a
(|*|) mx my = liftA2 (,) mx my >>= \(x, y) -> call (Mul x y)

infixr 7 |*|

(|==|) :: (Eq a) => GroupExpr a -> GroupExpr a -> GroupProp a
(|==|) = liftA2 (==)

infix 2 |==|

andProp :: Expr f Bool -> Expr f Bool -> Expr f Bool
andProp = liftA2 (&&)

lawAssoc :: (Eq a) => a -> a -> a -> GroupProp a
lawAssoc x y z = (pure x |*| pure y) |*| pure z |==| pure x |*| (pure y |*| pure z)

lawUnit, lawInv :: (Eq a) => a -> GroupProp a
lawUnit a = (pure a |*| gIdent |==| pure a) `andProp` (gIdent |*| pure a |==| pure a)
lawInv a = (pure a |*| gInv (pure a) |==| gIdent) `andProp` (gInv (pure a) |*| pure a |==| gIdent)

------------

-- |
--
-- >>> searchGroupOfOrder 2
-- [Solution [Ident := 0,Inv 0 := 0,Inv 1 := 1,Mul 0 0 := 0,Mul 0 1 := 1,Mul 1 0 := 1,Mul 1 1 := 0]]
searchGroupOfOrder :: Int -> [Solution (GroupSig Int)]
searchGroupOfOrder n = solve 10 initialModel equations >>= constraintToSolution
  where
    as = [0 .. n - 1]
    allValues = Set.fromList as
    allSigs = [Ident] ++ (Inv <$> as) ++ (Mul <$> as <*> as)
    initialModel = ModelConstraint $ DMap.fromList [sig :=> allValues | sig <- allSigs]

    equations = Map.fromList (eIsZero ++ equationsUnit ++ equationsInv ++ equationsAssoc)

    eIsZero = [("eIsZero", (== 0) <$> gIdent)]
    equationsUnit = [(name a, lawUnit a) | a <- as]
      where
        name a = "lawUnit " ++ show a
    equationsInv = [(name a, lawInv a) | a <- as]
      where
        name a = "lawInv " ++ show a
    equationsAssoc = [(name a b c, lawAssoc a b c) | a <- as, b <- as, c <- as]
      where
        name a b c = "lawAssoc " ++ show (a, b, c)

prettyPrintSolution :: Int -> Solution (GroupSig Int) -> IO ()
prettyPrintSolution n (Solution defs) = do
  putStrLn $ replicate (2 * n + 1) '-'
  for_ [0 .. n - 1] $ \x -> do
    for_ [0 .. n - 1] $ \y -> do
      let cell = maybe "?" show $ Map.lookup (x, y) multTable
      putStr $ cell ++ " "
    putStrLn ""
  putStrLn $ replicate (2 * n + 1) '-'
  where
    multTable :: Map.Map (Int, Int) Int
    multTable =
      Map.fromList $
        defs >>= \def ->
          case def of
            (Mul x y := z) -> [((x, y), z)]
            _ -> []

----------------
-- Instances
----------------


sigToRefl :: GroupSig a x -> a :~: x
sigToRefl Ident = Refl
sigToRefl (Inv _) = Refl
sigToRefl (Mul _ _) = Refl

deriving instance (Eq a) => Eq (GroupSig a x)

deriving instance (Ord a) => Ord (GroupSig a x)

deriving instance (Show a) => Show (GroupSig a x)

instance (Eq a) => GEq (GroupSig a) where
  geq sa sb = case (sigToRefl sa, sigToRefl sb) of
    (Refl, Refl) -> guard (sa == sb) *> Just Refl

instance (Ord a) => GCompare (GroupSig a) where
  gcompare sa sb = case (sigToRefl sa, sigToRefl sb) of
    (Refl, Refl) -> genOrdering (compare sa sb)

instance (Show a) => GShow (GroupSig a) where
  gshowsPrec = showsPrec

genOrdering :: Ordering -> GOrdering t t
genOrdering cmp = case cmp of
  LT -> GLT
  EQ -> GEQ
  GT -> GGT

instance (c a) => Has c (GroupSig a) where
  has sig body = case sigToRefl sig of Refl -> body

----
