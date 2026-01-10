module TraversableUtil where

import Data.FunctorShape
import Data.Traversable (mapAccumL, mapAccumM)
import Data.Foldable (toList)

indices :: Traversable f => f x -> f Int
indices = snd . mapAccumL (\n _ -> (succ n, n)) 0

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
