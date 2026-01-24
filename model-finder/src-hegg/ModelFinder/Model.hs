{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module ModelFinder.Model(
  Model(..),
  DumbModel(..), newDumbModel,
  SimpleModel(..), newSimpleModel,
  WrapperModel(..),
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Monad (guard)
import Data.Either (partitionEithers)
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (mapMaybe)
import Data.Coerce

-- | @model@ represents possible assignments @φ :: k -> a@.
-- 
-- * An assignment can be partial
-- * A model can represent /a priori/ knowledge about the assignments
--   (e.g. injectivity / "type" restriction / naturality / etc.)
class Model k a model | model -> k a where
  -- | Get the current possible assignments.
  -- Returning singleton means the value of @k@ is already settled.
  -- It can be empty if the model has gotten inconsistent.
  guess :: k -> model -> [a]

  -- | Get the intersection of guesses for the given multiple queries.
  guessMany :: NonEmpty k -> model -> [a]

  -- | Update the model accoring to newly added definitive equality @φ(k1) = φ(k2) = ... = y :: a@.
  -- Returns the updated model and newly discovered definitive equalities.
  -- Returns Nothing if the given equality is incompatible with model.
  enterDef :: [k] -> a -> model -> Maybe (model, [ (k, a) ])

  -- | Update the model accoring to newly added equality @φ(k1) = φ(k2) = ... = φ(kn)@.
  -- Returns the updated model and newly discovered definitive equalities.
  -- Returns Nothing if the given equality is incompatible with model.
  enterEqs :: [k] -> model -> Maybe (model, [ (k, a) ])
  enterEqs [] m = Just (m, [])
  enterEqs (k:ks) m = case guessMany (k :| ks) m of
    [] -> Nothing
    [a] -> enterDef ks a m >>= \(m', defs) -> Just (m', ((,a) <$> (k:ks)) ++ defs)
    _ -> Just (m, [])

-- | @DumbModel@ remember nothing and just returns
--   anything possible as @guess@.
newtype DumbModel k a = DumbModel { dumbUniverse :: [a] }
  deriving (Show, Eq)

newDumbModel :: [a] -> DumbModel k a
newDumbModel = DumbModel

instance Model k a (DumbModel k a) where
  guess _ = dumbUniverse 
  guessMany _ = dumbUniverse
  enterDef _ _ m = Just (m, [])
  enterEqs _ m = Just (m, [])

-- | @SimpleModel@ remembers a value for each specific @f a@.
--   The @guess@ returns set of arbitrary @a@ unless
--   the requested @f a@ value is remembered.  
data SimpleModel k a = SimpleModel {
    simpleUniverse :: [a],
    simpleGuesses :: !(Map k a)
  }
  deriving (Show, Eq)

newSimpleModel :: [a] -> SimpleModel k a
newSimpleModel univ = SimpleModel univ Map.empty

instance (Ord k, Ord a) => Model k a (SimpleModel k a) where
  guess k SimpleModel{ .. }
    = maybe simpleUniverse List.singleton $ Map.lookup k simpleGuesses

  guessMany :: NonEmpty k -> SimpleModel k a -> [a]
  guessMany (k :| ks) m = case rhsList of
      -- No definitions to propagate
      [] -> simpleUniverse m
      (a:as) -> guard (all (== a) as) *> [a]
    where
      rhsList = mapMaybe (`Map.lookup` simpleGuesses m) (k : ks)

  enterDef :: [k] -> a -> SimpleModel k a -> Maybe (SimpleModel k a, [(k, a)])
  enterDef ks a m = do
    guesses' <- loop ks (simpleGuesses m)
    pure (m{ simpleGuesses = guesses' }, [])
    where
      loop :: [k] -> Map k a -> Maybe (Map k a)
      loop [] guesses = pure guesses
      loop (k:rest) guesses = case Map.lookup k guesses of
        Nothing -> loop rest (Map.insert k a guesses)
        Just a' -> guard (a == a') *> loop rest (Map.insert k a guesses)

  enterEqs :: [k] -> SimpleModel k a -> Maybe (SimpleModel k a, [(k, a)])
  enterEqs [] m = pure (m, [])
  enterEqs ks m = case rhsList of
      -- No definitions to propagate
      [] -> pure (m, [])
      (a:as) -> guard (all (== a) as) *> addDefs a
    where
      guesses0 = simpleGuesses m

      lookupOrMissing k = case Map.lookup k guesses0 of
        Nothing -> Left k
        Just a  -> Right a

      (misses, rhsList) = partitionEithers (lookupOrMissing <$> ks)
      
      addDefs a = Just (m{ simpleGuesses = newGuesses}, newKnowns)
        where
          newKnowns = map (, a) misses
          -- Map.union is /left-biased/
          newGuesses = Map.union (Map.fromList newKnowns) guesses0

newtype WrapperModel k' k a model = WrapperModel {unwrapModel :: model}
  deriving (Show, Eq)

instance (Coercible k k', Model k a model) => Model k' a (WrapperModel k' k a model) where
  guess = coerce @(k -> model -> [a]) @_ guess
  guessMany = coerce @(NonEmpty k -> model -> [a]) @_ guessMany
  enterDef = coerce @([k] -> a -> model -> Maybe _) @_ enterDef
  enterEqs = coerce @([k] -> model -> Maybe _) @_ enterEqs