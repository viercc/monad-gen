{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

module ModelFinder.Model.PreNatMapModel(
  PreNatMapModel(..)
) where

import Control.Monad (guard)
import Data.Foldable (Foldable(toList))

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Foldable as F
import Data.Maybe (mapMaybe)
import qualified Data.Bitmap as Bitmap

import qualified Data.PreNatMap as PNM
import Data.PreNatMap (PreNatMap)

import Data.FunctorShape ( Shape(..), Ignored )
import ModelFinder.Model ( Model(..) )

import Data.Traversable.Extra (indices, zipMatchWith)

-- * BinaryJoin operation

-- * Model for BinaryJoin

data PreNatMapModel f g = PreNatMapModel
  {
    allShapes :: Set (Shape g),
    pnmGuesses :: PreNatMap f g
  }

deriving instance (Show (f Int), Show (g Int), Show (g Ignored), Traversable f, Functor g) => Show (PreNatMapModel f g)

instance
  (Traversable f, (forall a. Ord a => Ord (f a)),
   Traversable g, (forall a. Ord a => Ord (g a))) => Model (f Int) (g Int) (PreNatMapModel f g) where
  guess :: f Int -> PreNatMapModel f g -> [g Int]
  guess query m = case PNM.lookupWith Bitmap.singleton query (pnmGuesses m) of
      Nothing -> [ fa | Shape f <- Set.toList (allShapes m), fa <- traverse (const content) f ]
      Just gas -> traverse Bitmap.toList gas
    where
      content = Bitmap.toList . Bitmap.fromList . F.toList $ query
  
  enterDef :: [f Int] -> g Int -> PreNatMapModel f g
    -> Maybe (PreNatMapModel f g, [(f Int, g Int)])
  enterDef fas ga m = do
    let pnm = pnmGuesses m
    (pnm', newFullShapes) <- loop pnm Set.empty fas
    let newDefs = do
          Shape f <- Set.toList newFullShapes
          let lhsInt = indices f
          rhsInt <- toList $ PNM.fullMatch lhsInt pnm'
          pure (lhsInt, rhsInt)
    pure (m{ pnmGuesses = pnm' }, newDefs)
    where
      loop pnm newFull [] = pure (pnm, newFull)
      loop pnm newFull (fa : rest) = case PNM.match fa pnm of
        -- Do nothing for known result
        Just ga' -> guard (ga == ga') *> loop pnm newFull rest
        -- Refine for unknown result
        Nothing -> do
          pnm' <- PNM.refine fa ga pnm
          let -- If the refine made a "fully known" shape, record it
              newFull'
                | PNM.isFull (Shape fa) pnm' = Set.insert (Shape fa) newFull
                | otherwise = newFull
          loop pnm' newFull' rest

  enterEqs :: [f Int] -> PreNatMapModel f g
    -> Maybe (PreNatMapModel f g, [(f Int, g Int)])
  enterEqs fas m = case guesses of
    -- No guess is made for js
    [] -> Just (m, [])
    (guess0 : guesses') -> do
        -- Try to unify all guesses
        commonGuess <- unifyAllGuesses guess0 guesses'
        case traverse Bitmap.getSingleton commonGuess of
          Nothing -> Just (m, [])
          -- if the guess determines a unique answer,
          -- 'enterDef'.
          Just rhs -> enterDef fas rhs m
    where
      guessMaybe fa = PNM.lookupWith Bitmap.singleton fa (pnmGuesses m)
      guesses = mapMaybe guessMaybe fas
      unifyAllGuesses g [] = pure g
      unifyAllGuesses g (g' : rest) = do
        g'' <- zipMatchWith (\x y -> nonEmpty $ Bitmap.intersection x y) g g'
        unifyAllGuesses g'' rest
      nonEmpty x = x <$ guard (not (Bitmap.null x))
