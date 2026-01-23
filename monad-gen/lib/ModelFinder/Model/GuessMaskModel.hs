{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ModelFinder.Model.GuessMaskModel where

import ModelFinder.Model
import Control.Monad (guard)

data GuessMaskModel k a model = GuessMaskModel
   { guessMask :: k -> a -> Bool,
     rawModel :: model }

type GuessMaskModel' k a = GuessMaskModel k a (SimpleModel k a)

instance Model k a model => Model k a (GuessMaskModel k a model) where
  guess k m = filter (guessMask m k) $ guess k (rawModel m)

  guessMany ks m = filter (\a -> all (\k -> guessMask m k a) ks) $ guessMany ks (rawModel m)

  enterDef ks a m = do
    guard $ all (\k -> guessMask m k a) ks
    (sm', newDefs) <- enterDef ks a (rawModel m)
    pure (m{ rawModel = sm' }, newDefs)
  enterEqs fas m = do
    (sm', newDefs) <- enterEqs fas (rawModel m)
    pure (m{ rawModel = sm' }, newDefs)
