module Data.Traversable.Extra(
  Fresh, fresh, runFresh,

  indices, imap, zipMatch, zipMatchWith
) where

import Data.Traversable (mapAccumM)
import Data.Foldable (Foldable(toList))
import Data.FunctorShape
import Control.Monad.State.Strict

-- * Fresh

type Fresh = State Int

fresh :: Fresh Int
fresh = state (\i -> (i, i+1))

runFresh :: Fresh a -> a
runFresh fa = evalState fa 0

-- Custom traversals

indices :: Traversable t => t a -> t Int
indices = runFresh . traverse (const fresh)

imap :: Traversable t => (Int -> a -> b) -> t a -> t b
imap f = runFresh . traverse (\a -> (\i -> f i a) <$> fresh)

-- >>> zipMatch [1,2,3] "abc"
-- Just [(1,'a'),(2,'b'),(3,'c')]
-- >>> zipMatch [1,2] "abc"
-- Nothing
zipMatch :: (Eq (t Ignored), Traversable t) => t a -> t b -> Maybe (t (a,b))
zipMatch ta tb
  | Shape ta == Shape tb = snd <$> mapAccumM step (toList tb) ta
  | otherwise = Nothing
  where
    step [] _ = Nothing
    step (b:bs) a = Just (bs, (a,b))

zipMatchWith :: (Eq (t Ignored), Traversable t) => (a -> b -> Maybe c) -> t a -> t b -> Maybe (t c)
zipMatchWith op ta tb
  | Shape ta == Shape tb = snd <$> mapAccumM step (toList tb) ta
  | otherwise = Nothing
  where
    step [] _ = Nothing
    step (b:bs) a = op a b >>= \c -> Just (bs, c)
