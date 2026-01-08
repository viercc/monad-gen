{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main(main) where

import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as UV
import Data.PTraversable

import Targets (I')
import MonadGen
import System.IO (hPutStrLn, stderr)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

findCollisions :: forall k f. PTraversable f => [(k, MonadDict f)] -> [[k]]
findCollisions monadDictList =
    -- Maybe I should use hashtable rather than Map
    -- (to avoid comparison between vectors!)
    filter isMany . Map.elems . Map.fromListWith (++) $
      [ ((pureIndex dict, encodeTernaryOp (j dict)), [k]) | (k, dict) <- monadDictList ]
  where
    tab :: V.Vector (f Bool)
    tab = V.fromList (enum1 [False, True])
    
    n = V.length tab

    reverseIndexMap :: Map.Map (f Bool) Int
    reverseIndexMap = Map.fromList [ (a,i) | (i,a) <- V.toList (V.indexed tab) ]

    reverseIndex :: f Bool -> Int
    reverseIndex x = fromMaybe nonClosed $ Map.lookup x reverseIndexMap
      where
        -- this error happens only if @PTraversable f@ is implemented un-lawfully
        nonClosed = error "operator is not closed within the domain"

    encodeTernaryOp :: (f Bool -> f Bool -> f Bool -> f Bool) -> UV.Vector Int
    encodeTernaryOp op = UV.fromListN (n * n * n) $
        reverseIndex <$> (op <$> V.toList tab <*> V.toList tab <*> V.toList tab)

    -- Only needed to compare one value for @pure@
    pureIndex :: MonadDict f -> Int
    pureIndex monadDict = reverseIndex (_monadPure monadDict False)

    j :: MonadDict f -> f Bool -> f Bool -> f Bool -> f Bool
    j monadDict x y0 y1 = _monadJoin monadDict (fmap (\b -> if b then y1 else y0) x)

    isMany :: forall x. [x] -> Bool
    isMany xs = not (null (drop 1 xs))

main :: IO ()
main = do
  monadDataFileText <- readFile "output/I'/monad_data"
  case deserializeMonadDataList @I' (lines monadDataFileText) of
    Left err -> hPutStrLn stderr err
    Right monadDataList ->
      let dicts = makeMonadDict <$> monadDataList
      in mapM_ print $ findCollisions (zip [1 :: Int ..] dicts)