{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ModelFinder.Model.GuessMaskModel where

import ModelFinder.Model
import Control.Monad (guard)

data GuessMaskModel f a model = GuessMaskModel
   { guessMask :: f a -> a -> Bool,
     rawModel :: model }

instance Model f a model => Model f a (GuessMaskModel f a model) where
  guess fa m = filter (guessMask m fa) $ guess fa (rawModel m)
  enterDef fas a m = do
    guard $ all (\fa -> guessMask m fa a) fas
    (sm', newDefs) <- enterDef fas a (rawModel m)
    pure (m{ rawModel = sm' }, newDefs)
  enterEqs fas m = do
    (sm', newDefs) <- enterEqs fas (rawModel m)
    pure (m{ rawModel = sm' }, newDefs)
