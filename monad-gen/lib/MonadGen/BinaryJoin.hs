{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

module MonadGen.BinaryJoin where

import Data.Bool (bool)

import Control.Monad (guard)
import Data.Foldable (Foldable(toList))
import GHC.Generics ((:.:) (..))

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.PreNatMap as PNM
import Data.PreNatMap (PreNatMap)

import Data.FunctorShape
import ModelFinder.Model

import Data.PTraversable.Extra (_indices, _zipMatchWith)
import Data.Bits
import Data.Maybe (mapMaybe)

import ModelFinder.Term

-- * BinaryJoin operation

-- * Signature of join
data J x = J x x x
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

j :: Term J x -> Term J x -> Term J x -> Term J x
j x y0 y1 = fun (J x y0 y1)

-- Associativity of j
jAssoc :: ((x,x,x), x, x) -> (Term J x, Term J x)
jAssoc ((x, y0, y1), z0, z1) = (lhs, rhs)
  where
    lhs = j (j x' y0' y1') z0' z1'
    rhs = j x' (j y0' z0' z1') (j y1' z0' z1')

    x' = con x
    y0' = con y0
    y1' = con y1
    z0' = con z0
    z1' = con z1

-- naturality w.r.t. not
jNot :: Functor f => (f Bool, f Bool, f Bool) -> (Term J (f Bool), Term J (f Bool))
jNot (x, y0, y1) = (lhs, rhs)
  where
    lhs = j (con (not <$> x)) (con y0) (con y1)
    rhs = j (con x) (con y1) (con y0)

-- naturality w.r.t. constant join
jConst :: Functor f => Shape f -> f Bool -> f Bool -> (Term J (f Bool), Term J (f Bool))
jConst (Shape x_) y0 y1 = (lhs, rhs)
  where
    x' = con (False <$ x_)
    lhs = j x' (con y0) (con y1)
    rhs = j x' (con y0) (con y0)

-- left unit law
jUnitLeft :: Functor f => Shape f -> f Bool -> f Bool -> (J (f Bool), f Bool)
jUnitLeft (Shape u_) y0 y1 = (lhs, rhs)
  where
    lhs = J (False <$ u_) y0 y1
    rhs = y0

-- right unit law
jUnitRight :: Functor f => Shape f -> f Bool -> (J (f Bool), f Bool)
jUnitRight (Shape u_) x = (lhs, rhs)
  where
    lhs = J x (False <$ u_) (False <$ u_)
    rhs = x

-- Special case for an empty value
jZero :: (Traversable f) => Shape f -> [f Bool -> f Bool -> (J (f Bool), f Bool)]
jZero (Shape z_) = case traverse (const Nothing) z_ of
  Nothing -> []
  Just z  -> [\y0 y1 -> (J z y0 y1, z)]

data BinaryJoin f a = BJ (f Bool) (f a) (f a)
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (f Bool), Show (f x)) => Show (BinaryJoin f x)
deriving instance (Eq (f Bool), Eq (f x)) => Eq (BinaryJoin f x)
deriving instance (Ord (f Bool), Ord (f x)) => Ord (BinaryJoin f x)

fromJ :: J (f Bool) -> BinaryJoin f Bool
fromJ (J x y0 y1) = BJ x y0 y1

-- * Model for BinaryJoin

data BinaryJoinModel f = BinaryJoinModel
  {
    allShapes :: Set (Shape f),
    joinPreNatMap :: PreNatMap (BinaryJoin f) f,
    givenInputs :: Set (J (f Bool))
  }

data AmbBool =
    F -- ^ \"false\"
  | T -- ^ \"true\"
  | U -- ^ ambiguous
  deriving (Eq, Ord)

instance Semigroup AmbBool where
  U <> _ = U
  _ <> U = U
  F <> F = F
  F <> T = U
  T <> F = U
  T <> T = T

amb :: Bool -> AmbBool
amb = bool F T

selectAmb :: AmbBool -> [Bool]
selectAmb a = case a of
  F -> [False]
  T -> [True]
  U -> [False, True]

uniqueBool :: AmbBool -> Maybe Bool
uniqueBool a = case a of
  F -> Just False
  T -> Just True
  U -> Nothing

unifyAmbBool :: AmbBool -> AmbBool -> Maybe AmbBool
unifyAmbBool x y = case x of
  U -> Just y
  F -> case y of
    T -> Nothing
    _ -> Just F
  T -> case y of
    F -> Nothing
    _ -> Just T

instance (Traversable f, (forall a. Ord a => Ord (f a))) => Model J (f Bool) (BinaryJoinModel f) where
  universe m = Set.fromList [ fb | (Shape f) <- Set.toList (allShapes m), fb <- sequenceA ([False, True] <$ f)]

  guess query m =
    let ff = amb <$> fromJ query
    in case PNM.lookup ff (joinPreNatMap m) of
         Nothing -> universe m
         Just fa -> Set.fromList $ traverse selectAmb fa

  enterDef js rhs m = do
    let pnm = joinPreNatMap m
    (pnm', newFullShapes) <- loop pnm Set.empty js
    let newDefs = do
          Shape ff <- Set.toList newFullShapes
          let lhsInt = _indices ff
          rhsInt <- toList $ PNM.fullMatch lhsInt pnm'
          pure (Shape lhsInt, rhsInt)
    pure (m{ joinPreNatMap = pnm' }, newDefs >>= makeBinaryJoinDefs)
    where
      loop pnm newFull [] = pure (pnm, newFull)
      loop pnm newFull (query : rest) = case PNM.match ff pnm of
        -- Do nothing for known result
        Just y -> guard (rhs == y) *> loop pnm newFull rest
        -- Refine for unknown result
        Nothing -> do
          pnm' <- PNM.refine ff rhs pnm
          let -- If the refine made a "fully known" shape, record it
              newFull'
                | PNM.isFull (Shape ff) pnm' = Set.insert (Shape ff) newFull
                | otherwise = newFull
          loop pnm' newFull' rest
        where
          ff = fromJ query

  enterEqs ::
    [J (f Bool)]
    -> BinaryJoinModel f
    -> Maybe (BinaryJoinModel f, [(J (f Bool), f Bool)])
  enterEqs js m = case guesses of
    -- No guess is made for js
    [] -> Just (m, [])
    (guess0 : guesses') -> do 
        -- Try to unify all guesses
        commonGuess <- unifyAllGuesses guess0 guesses'
        case traverse uniqueBool commonGuess of
          Nothing -> Just (m, [])
          -- if the guess determines a unique answer,
          -- 'enterDef'.
          Just rhs -> enterDef js rhs m
    where
      guessMaybe query = PNM.lookup (amb <$> fromJ query) (joinPreNatMap m)
      guesses = mapMaybe guessMaybe js
      unifyAllGuesses g [] = pure g
      unifyAllGuesses g (g' : rest) = do
        g'' <- _zipMatchWith unifyAmbBool g g'
        unifyAllGuesses g'' rest

makeBinaryJoinDefs :: Traversable f => (Shape (BinaryJoin f), f Int) -> [(J (f Bool), f Bool)]
makeBinaryJoinDefs (Shape (BJ x y0 y1), rhs) =
  do (bitmap0, yBool0) <- boolTable y0
     (bitmap1, yBool1) <- boolTable y1
     let bitmap = shiftL bitmap0 (length y1) .|. bitmap1
         rhsBool = testBit bitmap <$> rhs
     pure (J x yBool0 yBool1, rhsBool)

type Bitmap = Word

boolTable :: Traversable f => f any -> [(Bitmap, f Bool)]
boolTable f
  | n <= lenMax = mk <$> [0 .. 2 ^ n - 1]
  | otherwise = error $ "too long: " ++ show n ++ " >= " ++ show lenMax
  where
    lenMax = finiteBitSize (0 :: Word) `div` 2
    n = length f
    fi = _indices f
    mk bitmap = (bitmap, testBit bitmap <$> fi)
