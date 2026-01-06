{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ModelFinder.Model(
  Model(..),
  DumbModel(..), newDumbModel,
  SimpleModel(..), newSimpleModel,
) where

import Data.Kind (Type)
import Data.Set (Set)
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad (guard)
import Data.Either (partitionEithers)

-- | @model@ represents possible assignments of @a@ to @f a@.

class Model f a model | model -> f a where
  -- | Set of all possible values.
  universe :: model -> Set a

  -- | Get the current possible assignments.
  -- Returning singleton means the value of @f a@ is already settled.
  -- It can be empty if the model has gotten inconsistent.
  guess :: f a -> model -> Set a

  -- | Update the model accoring to newly added definitive equality @(x1 :: f a) = (x2 :: f a) = ... = (y :: a)@.
  -- Returns the updated model and newly discovered definitive equalities.
  -- Returns Nothing if the given equality is incompatible with model.
  enterDef :: [f a] -> a -> model -> Maybe (model, [ (f a, a) ])

  -- | Update the model accoring to newly added equality @(x1 :: f a) = (x2 :: f a) = ... = (xn :: f a)@.
  -- Returns the updated model and newly discovered definitive equalities.
  -- Returns Nothing if the given equality is incompatible with model.
  enterEqs :: [f a] -> model -> Maybe (model, [ (f a, a) ])

-- | @DumbModel@ remember nothing and just returns
--   anything possible as @guess@.
newtype DumbModel (f :: Type -> Type) a = DumbModel { dumbUniverse :: Set a }
  deriving (Show, Eq)

newDumbModel :: Set a -> DumbModel f a
newDumbModel = DumbModel

instance Model f a (DumbModel f a) where
  universe = dumbUniverse
  guess _ = universe
  enterDef _ _ m = Just (m, [])
  enterEqs _ m = Just (m, [])

-- | @SimpleModel@ remembers a value for each specific @f a@.
--   The @guess@ returns set of arbitrary @a@ unless
--   the requested @f a@ value is remembered.  
data SimpleModel f a = SimpleModel {
    simpleUniverse :: !(Set a),
    simpleGuesses :: !(Map (f a) a)
  }
  deriving (Show, Eq)

newSimpleModel :: Set a -> SimpleModel f a
newSimpleModel univ = SimpleModel univ Map.empty

instance (Ord (f a), Ord a) => Model f a (SimpleModel f a) where
  universe = simpleUniverse

  guess fa SimpleModel{ .. }
    = maybe simpleUniverse Set.singleton $ Map.lookup fa simpleGuesses

  enterDef :: [f a] -> a -> SimpleModel f a -> Maybe (SimpleModel f a, [(f a, a)])
  enterDef fas a m = do
    guesses' <- loop fas (simpleGuesses m)
    pure (m{ simpleGuesses = guesses' }, [])
    where
      loop :: [f a] -> Map (f a) a -> Maybe (Map (f a) a)
      loop [] guesses = pure guesses
      loop (fa:rest) guesses = case Map.lookup fa guesses of
        Nothing -> loop rest (Map.insert fa a guesses)
        Just a' -> guard (a == a') *> loop rest (Map.insert fa a guesses)

  enterEqs :: [f a] -> SimpleModel f a -> Maybe (SimpleModel f a, [(f a, a)])
  enterEqs [] m = pure (m, [])
  enterEqs fas m = case rhsList of
      -- No definitions to propagate
      [] -> pure (m, [])
      (a:as) -> guard (all (== a) as) *> addDefs a
    where
      guesses0 = simpleGuesses m

      lookupOrMissing fa = case Map.lookup fa guesses0 of
        Nothing -> Left fa
        Just a  -> Right a

      (misses, rhsList) = partitionEithers (lookupOrMissing <$> fas)
      
      addDefs a = Just (m{ simpleGuesses = newGuesses}, newKnowns)
        where
          newKnowns = map (, a) misses
          -- Map.union is /left-biased/
          newGuesses = Map.union (Map.fromList newKnowns) guesses0

