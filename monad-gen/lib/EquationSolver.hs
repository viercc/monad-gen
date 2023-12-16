{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
module EquationSolver(
  Expr(..),
  Definition(..),
  DefTable,

  Equation(..),
  Guesser,
  genDefTables
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Foldable (Foldable(..))
import Data.Ord (comparing)
import Data.List (maximumBy)

data Expr f a = Leaf a | Node (f (Expr f a))
    deriving (Functor)

-- It is sufficient to require that:
--   (Eq a, forall b. Eq b => Eq (f b))
-- but it's just easier to use common constraint with Ord.
instance (Ord a, forall b. Ord b => Ord (f b)) => Eq (Expr f a) where
  Leaf a == Leaf a' = a == a'
  Leaf _ == Node _ = False
  Node _ == Leaf _ = False
  Node fe == Node fe' = fe == fe'

instance (Ord a, forall b. Ord b => Ord (f b)) => Ord (Expr f a) where
  compare (Leaf a) (Leaf a') = compare a a'
  compare (Leaf _) (Node _) = LT
  compare (Node _) (Leaf _) = GT
  compare (Node fe) (Node fe') = compare fe fe'

data Definition f a = Define (f a) a
    deriving (Eq, Ord, Functor)

type DefTable f a = Map.Map (f a) a

getLeaf :: Expr f a -> Maybe a
getLeaf (Leaf a) = Just a
getLeaf _ = Nothing

reduce :: (Ord (f a), Traversable f) => DefTable f a -> Expr f a -> Expr f a
reduce table = go
  where
    go (Leaf x) = Leaf x
    go (Node fe) =
      let fe' = go <$> fe
      in case traverse getLeaf fe' >>= (`Map.lookup` table) of
           Nothing -> Node fe'
           Just x -> Leaf x

-- * Equations

data Equation f a = Equals (Expr f a) (Expr f a)
    deriving (Functor)

infix 2 `Equals`

deriving instance (Ord a, forall b. Ord b => Ord (f b)) => Eq (Equation f a)
deriving instance (Ord a, forall b. Ord b => Ord (f b)) => Ord (Equation f a)

newtype Blocker f a = Blocker { getBlockerMap :: Map.Map (f a) (Set.Set (Equation f a)) }

instance (Ord a, forall b. Ord b => Ord (f b)) => Semigroup (Blocker f a) where
  Blocker bm <> Blocker bm' = Blocker $ Map.unionWith Set.union bm bm'
instance (Ord a, forall b. Ord b => Ord (f b)) => Monoid (Blocker f a) where
  mempty = Blocker Map.empty

mostWanted :: Blocker f a -> Maybe (f a)
mostWanted blocker
  | Map.null bm = Nothing
  | otherwise   = Just $ fst $ maximumBy (comparing (Set.size . snd)) $ Map.toList bm
  where
    bm = getBlockerMap blocker

checkEquation :: (Ord a, forall b. Ord b => Ord (f b), Traversable f) => DefTable f a -> Equation f a -> Maybe (Blocker f a, [Definition f a])
checkEquation table (Equals e1 e2) = case (reduce table e1, reduce table e2) of
  (Leaf x1, Leaf x2)
    | x1 == x2 -> Just mempty
    | otherwise -> Nothing
  (Node fe1', Leaf x2) -> Just $ oneSidedCase fe1' x2
  (Leaf x1, Node fe2') -> Just $ oneSidedCase fe2' x1
  (e1', e2') -> Just (collectBlockers (e1' `Equals` e2'), [])

oneSidedCase :: (Traversable f, Ord a, forall b. Ord b => Ord (f b)) => f (Expr f a) -> a -> (Blocker f a, [Definition f a])
oneSidedCase fe x = case traverse getLeaf fe of
  Just fx -> (mempty, [Define fx x])
  Nothing -> (collectBlockers (Node fe `Equals` Leaf x), [])

collectBlockers :: (Traversable f, Ord (f a)) => Equation f a -> Blocker f a
collectBlockers eqn@(Equals e1 e2) = Blocker $ Map.fromList [ (b, Set.singleton eqn) | b <- blockerNode e1 ++ blockerNode e2 ]

blockerNode :: Traversable f => Expr f a -> [f a]
blockerNode (Leaf _) = []
blockerNode (Node fe) = case traverse getLeaf fe of
  Nothing -> foldMap blockerNode fe
  Just fx -> [fx]

checkEquations :: (Traversable f, Ord a, forall b. Ord b => Ord (f b), Foldable t) => DefTable f a -> t (Equation f a) -> Maybe (Blocker f a, [Definition f a])
checkEquations table equations = fmap fold $ traverse (checkEquation table) $ toList equations

type Guesser f a = f a -> [a]

genDefTables :: (Traversable f, Ord a, forall b. Ord b => Ord (f b)) => Guesser f a -> [Equation f a] -> [DefTable f a]
genDefTables guess allEquations = case checkEquations Map.empty allEquations of
  Nothing -> []
  Just (blockers, defs) -> go Map.empty blockers defs
  where
    go table blocker [] = case mostWanted blocker of
      Nothing -> [table]
      Just fx -> do
        y <- guess fx
        case enter table (Define fx y) blocker of
          Nothing -> []
          Just (table', blocker', newDefs) -> go table' blocker' newDefs
    go table blocker (def : defs)  =
      case enter table def blocker of
        Nothing -> []
        Just (table', blocker', newDefs) -> go table' blocker' (newDefs ++ defs)

enter :: (Traversable f, Ord a, forall b. Ord b => Ord (f b))
  => DefTable f a -> Definition f a -> Blocker f a
  -> Maybe (DefTable f a, Blocker f a, [Definition f a])
enter table (Define fx y) (Blocker bm) =
  case Map.lookup fx table of
    Nothing ->
      let eqs = Map.findWithDefault Set.empty fx bm
          table' = Map.insert fx y table
          blocker' = Blocker $ Map.delete fx bm
      in case checkEquations table' eqs of
           Nothing -> Nothing
           Just (newBlocker, newDefs) -> Just (table', newBlocker <> blocker', newDefs)
    Just y' | y == y' -> Just (table, Blocker bm, [])
            | otherwise -> Nothing
