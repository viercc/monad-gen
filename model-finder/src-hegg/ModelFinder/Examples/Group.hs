{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}

module ModelFinder.Examples.Group(
  GroupSig(..),
  searchGroupOfOrder,
  prettyPrintSolution,

  GroupModel(..),
  Bijection(..),
  searchGroupOfOrder'
) where

import Data.Foldable (for_)

import Data.Map qualified as Map
import Data.Set qualified as Set

import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Bifunctor (Bifunctor(..))
import Control.Monad (guard)

import ModelFinder.Model
import ModelFinder.Solver
import qualified Data.List.NonEmpty as NE
import Data.Foldable1 (foldl1')

-- | Signature of functions which defines group structure on @a@.
data GroupSig a = Ident | Inv a | Mul a a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

----

type GroupExpr a = Term GroupSig a
type Solution a = Map (GroupSig a) a

identity :: GroupExpr a
identity = liftFun Ident

inv :: GroupExpr a -> GroupExpr a
inv a = fun (Inv a)

(☆) :: GroupExpr a -> GroupExpr a -> GroupExpr a
(☆) x y = fun (Mul x y)

infix 7 ☆

lawAssoc :: Property GroupSig
lawAssoc = Property $
  ForAll \x ->
    ForAll \y ->
      ForAll \z ->
        Equals ((con x ☆ con y) ☆ con z) (con x ☆ (con y ☆ con z))

lawUnit1, lawUnit2, lawInv1, lawInv2 :: Property GroupSig
lawUnit1 = Property $ ForAll \a -> (con a ☆ identity) `Equals` con a
lawUnit2 = Property $ ForAll \a -> (identity ☆ con a) `Equals` con a
lawInv1 = Property $ ForAll \a -> (con a ☆ inv (con a)) `Equals` identity 
lawInv2 = Property $ ForAll \a -> (inv (con a) ☆ con a) `Equals` identity

groupEquations :: [Property GroupSig]
groupEquations = [lawAssoc, lawUnit1, lawUnit2, lawInv1, lawInv2]

prettyPrintSolution :: Int -> Solution Int -> IO ()
prettyPrintSolution n defs = do
  putStrLn $ replicate (2 * n + 1) '-'
  for_ [1 .. n] $ \x -> do
    for_ [1 .. n] $ \y -> do
      let cell = maybe "?" show $ Map.lookup (Mul x y) defs
      putStr $ cell ++ " "
    putStrLn ""
  putStrLn $ replicate (2 * n + 1) '-'

------------

-- |
--
-- >>> searchGroupOfOrder 2
-- [fromList [(Ident,1),(Inv 1,1),(Inv 2,2),(Mul 1 1,1),(Mul 1 2,2),(Mul 2 1,2),(Mul 2 2,1)]]
--
-- >>> searchGroupOfOrder 3
-- [fromList [(Ident,1),(Inv 1,1),(Inv 2,3),(Inv 3,2),(Mul 1 1,1),(Mul 1 2,2),(Mul 1 3,3),(Mul 2 1,2),(Mul 2 2,3),(Mul 2 3,1),(Mul 3 1,3),(Mul 3 2,1),(Mul 3 3,2)]]
-- 
-- >>> length $ searchGroupOfOrder 4
-- 4

-- >>> length $ searchGroupOfOrder 5
-- 6
searchGroupOfOrder :: Int -> [Solution Int]
searchGroupOfOrder n = map simpleGuesses $ solve univ groupEquations initialDef model0
  where
    univ = [1..n]
    model0 = newSimpleModel univ
    initialDef = Map.fromList [ (Ident, 1) ]

-- * Model with more knowledge

-- "Model" used for the model search can have a knowlege about the model.
-- For example, a group operations have the following properties.
--
-- 1. @inv :: a -> a@ is bijection
-- 2. @(x ☆) :: a -> a@ is bijection for all x
--
-- A specialized GroupModel using property 1. and 2. can be made like follows:

---- Bijections

data Bijection a = BijData { knownBij :: !(Map a a), unusedVal :: Set a }

emptyBij :: Set a -> Bijection a
emptyBij as = BijData { knownBij = Map.empty, unusedVal = as }

insertBij :: Ord a => a -> a -> Bijection a -> Maybe (Bijection a)
insertBij x y (BijData known unused) = case Map.lookup x known of
  Nothing | y `Set.member` unused -> Just bij'
  Just y' | y == y' -> Just bij'
  _ -> Nothing
  where
    known' = Map.insert x y known
    unused' = Set.delete y unused
    bij' = BijData known' unused'

guessBij :: Ord a => a -> Bijection a -> Set a
guessBij a (BijData known unused) = maybe unused Set.singleton $ Map.lookup a known

lastOne :: Ord a => Bijection a -> ([(a,a)], Bijection a)
lastOne bij@(BijData known unused)
  | Set.size unused == 1 = ([(b,a)], BijData known' Set.empty)
  | otherwise = ([], bij)
  where
    a = Set.findMin unused
    as = Set.fromList (Map.elems known)
    
    bs = Map.keysSet known
    b = Set.findMin $ Set.insert a as Set.\\ bs
    known' = Map.insert b a known

---- GroupModel

data GroupModel a = GroupModel {
    groupUniverse :: Set a,
    groupIdentGuess :: Maybe a,
    groupInvGuess :: Bijection a,
    groupMulGuess :: Map a (Bijection a)
  }

newGroupModel :: Set a -> GroupModel a
newGroupModel univ = GroupModel{
    groupUniverse = univ,
    groupIdentGuess = Nothing,
    groupInvGuess = emptyBij univ,
    groupMulGuess = Map.empty
  }

groupModelToSolution :: Ord a => GroupModel a -> Solution a
groupModelToSolution m = Map.fromList $ identDef ++ invDefs ++ mulDefs
  where
    identDef = [ (Ident, a) | Just a <- [groupIdentGuess m] ]
    invDefs = [ (Inv b, a) | (b,a) <- Map.toList (knownBij (groupInvGuess m)) ]
    mulDefs = [ (Mul x y, a) |
      (x, bij) <- Map.toList (groupMulGuess m),
      (y,a) <- Map.toList (knownBij bij) ]

guessGroup :: Ord a => GroupSig a -> GroupModel a -> Set a
guessGroup sig m = case sig of
  Ident -> maybe (groupUniverse m) Set.singleton $ groupIdentGuess m
  Inv a -> guessBij a (groupInvGuess m)
  Mul a b -> case Map.lookup a (groupMulGuess m) of
    Nothing -> groupUniverse m
    Just bij -> guessBij b bij

instance Ord a => Model (GroupSig a) a (GroupModel a) where
  guess :: GroupSig a -> GroupModel a -> [a]
  guess sig m = Set.toList $ guessGroup sig m
  
  guessMany :: NE.NonEmpty (GroupSig a) -> GroupModel a -> [a]
  guessMany sigs m = Set.toList commonGuess
    where
      commonGuess = foldl1' Set.intersection $ (`guessGroup` m) <$> sigs

  enterDef :: [GroupSig a] -> a -> GroupModel a -> Maybe (GroupModel a, [(GroupSig a, a)])
  enterDef sigs a m0 = loop m0 [] sigs
    where
      loop m acc [] = pure (m, acc)
      loop m acc (sig : rest) = case sig of
        Ident -> unifyMaybe (Just a) (groupIdentGuess m) >>= \idGuess ->
          let m' = m{ groupIdentGuess = idGuess }
          in loop m' acc rest
        Inv b -> insertBij b a (groupInvGuess m) >>= \invGuess ->
          let (newEntry, invGuess') = lastOne invGuess
              m' = m{ groupInvGuess = invGuess' }
              newDefs = map (first Inv) newEntry
          in loop m' (newDefs ++ acc) rest
        Mul x y -> case Map.lookup x (groupMulGuess m) of
          Nothing -> do
            newBij <- insertBij y a $ emptyBij (groupUniverse m)
            let mulGuess' = Map.insert x newBij (groupMulGuess m)
                m' = m{ groupMulGuess = mulGuess' }
            loop m' acc rest
          Just bij -> do
            bij' <- insertBij y a bij
            let (newEntry, bij'') = lastOne bij'
                newDefs = map (first (Mul x)) newEntry
                mulGuess' = Map.insert x bij'' (groupMulGuess m)
                m' = m{ groupMulGuess = mulGuess' }
            loop m' (newDefs ++ acc) rest

unifyMaybe :: Eq a => Maybe a -> Maybe a -> Maybe (Maybe a)
unifyMaybe Nothing y = Just y
unifyMaybe (Just x) Nothing = Just (Just x)
unifyMaybe (Just x) (Just y) = Just x <$ guard (x == y)

-- | Solve using GroupModel
--
-- >>> searchGroupOfOrder' 3
-- [fromList [(Ident,1),(Inv 1,1),(Inv 2,3),(Inv 3,2),(Mul 1 1,1),(Mul 1 2,2),(Mul 1 3,3),(Mul 2 1,2),(Mul 2 2,3),(Mul 2 3,1),(Mul 3 1,3),(Mul 3 2,1),(Mul 3 3,2)]]
--
-- >>> length $ searchGroupOfOrder' 5
-- 6
-- 
-- >>> length $ searchGroupOfOrder' 7
-- 120
searchGroupOfOrder' :: Int -> [Solution Int]
searchGroupOfOrder' n = map groupModelToSolution $ solve univ groupEquations initialDef model0
  where
    univ = [1..n]
    model0 = newGroupModel (Set.fromList univ)
    initialDef = Map.fromList [ (Ident, 1) ]
