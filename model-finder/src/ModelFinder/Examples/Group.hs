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

import ModelFinder.Expr
import ModelFinder.Solver

-- | Signature of functions which defines group structure on @a@.
data GroupSig a x where
  Ident :: GroupSig a a
  Inv :: a -> GroupSig a a
  Mul :: a -> a -> GroupSig a a

----

type GroupExpr a = Expr (GroupSig a) a
type GroupProp a = Property (GroupSig a)

gIdent :: GroupExpr a
gIdent = lift0 Ident

gInv :: GroupExpr a -> GroupExpr a
gInv = lift1 Inv

(|*|) :: GroupExpr a -> GroupExpr a -> GroupExpr a
(|*|) = lift2 Mul

infixr 7 |*|

lawAssoc :: (Eq a) => a -> a -> a -> GroupProp a
lawAssoc x y z = (pure x |*| pure y) |*| pure z === pure x |*| (pure y |*| pure z)

lawUnit1, lawUnit2, lawInv1, lawInv2 :: (Eq a) => a -> GroupProp a
lawUnit1 a = pure a |*| gIdent `evaluatesTo` a
lawUnit2 a = gIdent |*| pure a `evaluatesTo` a
lawInv1 a = pure a |*| gInv (pure a) === gIdent 
lawInv2 a = gInv (pure a) |*| pure a === gIdent

------------

-- |
--
-- >>> searchGroupOfOrder 2
-- [Solution [Ident := 0,Inv 0 := 0,Inv 1 := 1,Mul 0 0 := 0,Mul 0 1 := 1,Mul 1 0 := 1,Mul 1 1 := 0]]
searchGroupOfOrder :: Int -> [Solution (GroupSig Int)]
searchGroupOfOrder n = solve 10 initialModel eqMap >>= constraintToSolution
  where
    as = [0 .. n - 1]
    allValues = Set.fromList as
    initialModel = Model $ DMap.fromList $
      [Ident :=> Set.singleton 0] ++
      [ sig :=> allValues | sig <- Inv <$> as] ++
      [ sig :=> allValues | sig <- Mul <$> as <*> as]

    equations = concat [
        lawUnit1 <$> as,
        lawUnit2 <$> as,
        lawInv1 <$> as,
        lawInv2 <$> as,
        lawAssoc <$> as <*> as <*> as
      ]
    eqMap = Map.fromList (zip [0 :: Int ..] equations)

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
