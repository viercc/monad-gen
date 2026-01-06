{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ModelFinder.Model.GuessMaskModel where

import ModelFinder.Model
import qualified Data.Set as Set
import Control.Monad (guard)

data GuessMaskModel f a = GuessMaskModel
   { guessMask :: f a -> a -> Bool,
     simpleModel :: SimpleModel f a }

instance (Ord a, Traversable f, Ord (f a)) => Model f a (GuessMaskModel f a) where
  universe = universe . simpleModel
  guess fa m = Set.filter (guessMask m fa) (guess fa (simpleModel m))
  enterDef fas a m = do
    guard $ all (\fa -> guessMask m fa a) fas
    (sm', newDefs) <- enterDef fas a (simpleModel m)
    pure (m{ simpleModel = sm' }, newDefs)
  enterEqs fas m = do
    (sm', newDefs) <- enterEqs fas (simpleModel m)
    pure (m{ simpleModel = sm' }, newDefs)
