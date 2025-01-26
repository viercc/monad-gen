{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main(main) where

import Data.Coerce (coerce)
import Data.Maybe (mapMaybe)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Finite (finite)
import qualified Data.Vector.Sized as SV

import StoreDistributiveLaw
import Data.Finitary
import Data.Functor.Classes (showsUnaryWith, showsBinaryWith)
import Data.Foldable (for_)

main :: IO ()
main = prettyPrintDistLenses

generateAllDistLaws :: IO ()
generateAllDistLaws = mapM_ (print . encodeLens) $ lawfulDistLenses (candidateLenses ())

{- Output (took about 18 min.):

LensEnc (Vector [(finite 0,finite 39),(finite 0,finite 54),(finite 4,finite 54),(finite 4,finite 39),(finite 3,finite 39),(finite 7,finite 99),(finite 3,finite 99),(finite 7,finite 39)])
LensEnc (Vector [(finite 0,finite 39),(finite 1,finite 57),(finite 6,finite 198),(finite 4,finite 39),(finite 3,finite 39),(finite 5,finite 147),(finite 2,finite 108),(finite 7,finite 39)])
LensEnc (Vector [(finite 1,finite 45),(finite 0,finite 54),(finite 4,finite 54),(finite 6,finite 135),(finite 2,finite 45),(finite 7,finite 99),(finite 3,finite 99),(finite 5,finite 135)])
LensEnc (Vector [(finite 1,finite 45),(finite 1,finite 57),(finite 6,finite 198),(finite 6,finite 135),(finite 2,finite 45),(finite 5,finite 147),(finite 2,finite 108),(finite 5,finite 135)])

-}

generatedData :: [ LensEnc (C A A B) (A,B) (C B B A) (B,A) ]
generatedData = mapMaybe (fmap LensEnc)
  [
    SV.fromList [(finite 0,finite 39),(finite 0,finite 54),(finite 4,finite 54),(finite 4,finite 39),(finite 3,finite 39),(finite 7,finite 99),(finite 3,finite 99),(finite 7,finite 39)]
  , SV.fromList [(finite 0,finite 39),(finite 1,finite 57),(finite 6,finite 198),(finite 4,finite 39),(finite 3,finite 39),(finite 5,finite 147),(finite 2,finite 108),(finite 7,finite 39)]
  , SV.fromList [(finite 1,finite 45),(finite 0,finite 54),(finite 4,finite 54),(finite 6,finite 135),(finite 2,finite 45),(finite 7,finite 99),(finite 3,finite 99),(finite 5,finite 135)]
  , SV.fromList [(finite 1,finite 45),(finite 1,finite 57),(finite 6,finite 198),(finite 6,finite 135),(finite 2,finite 45),(finite 5,finite 147),(finite 2,finite 108),(finite 5,finite 135)]
  ]

prettyPrintDistLenses :: IO ()
prettyPrintDistLenses = for_ (zip [0 :: Int ..] generatedData) $ \(i, encLens) -> do
  let lens = decodeLens encLens
  putStrLn $ "Dist #" ++ show i
  for_ (prettyPrintDistLens lens) $ \pprLine ->
    putStrLn $ "  " ++ pprLine

{- Output:

Dist #0
  let q (A₀,B₀,B₀) = (B₀,A₀,A₀)
      q (A₀,B₀,B₁) = (B₀,A₀,A₀)
      q (A₀,B₁,B₀) = (B₁,A₀,A₀)
      q (A₀,B₁,B₁) = (B₁,A₀,A₀)
      q (A₁,B₀,B₀) = (B₀,A₁,A₁)
      q (A₁,B₀,B₁) = (B₁,A₁,A₁)
      q (A₁,B₁,B₀) = (B₀,A₁,A₁)
      q (A₁,B₁,B₁) = (B₁,A₁,A₁)
      d0 (A₀,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₀) (B₁,A₀) = A₀
      d0 (A₀,B₀,B₀) (B₁,A₁) = A₁
      d0 (A₀,B₀,B₁) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₁) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₁) (B₁,A₀) = A₀
      d0 (A₀,B₀,B₁) (B₁,A₁) = A₁
      d0 (A₀,B₁,B₀) (B₀,A₀) = A₀
      d0 (A₀,B₁,B₀) (B₀,A₁) = A₁
      d0 (A₀,B₁,B₀) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₀) (B₁,A₁) = A₁
      d0 (A₀,B₁,B₁) (B₀,A₀) = A₀
      d0 (A₀,B₁,B₁) (B₀,A₁) = A₁
      d0 (A₀,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₁,A₀) = A₀
      d0 (A₁,B₀,B₀) (B₁,A₁) = A₁
      d0 (A₁,B₀,B₁) (B₀,A₀) = A₀
      d0 (A₁,B₀,B₁) (B₀,A₁) = A₁
      d0 (A₁,B₀,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₀,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₁,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₁,A₀) = A₀
      d0 (A₁,B₁,B₀) (B₁,A₁) = A₁
      d0 (A₁,B₁,B₁) (B₀,A₀) = A₀
      d0 (A₁,B₁,B₁) (B₀,A₁) = A₁
      d0 (A₁,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₁,B₁) (B₁,A₁) = A₁
      d1 (A₀,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₀,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₁) (B₀,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₁,A₀) = B₁
      d1 (A₀,B₀,B₁) (B₁,A₁) = B₀
      d1 (A₀,B₁,B₀) (B₀,A₀) = B₀
      d1 (A₀,B₁,B₀) (B₀,A₁) = B₁
      d1 (A₀,B₁,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₀) (B₁,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₁,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₁,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₁) (B₀,A₀) = B₁
      d1 (A₁,B₀,B₁) (B₀,A₁) = B₀
      d1 (A₁,B₀,B₁) (B₁,A₀) = B₀
      d1 (A₁,B₀,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₀) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₀) (B₁,A₀) = B₀
      d1 (A₁,B₁,B₀) (B₁,A₁) = B₁
      d1 (A₁,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₁,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₁,B₁,B₁) (B₁,A₁) = B₁
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))
Dist #1
  let q (A₀,B₀,B₀) = (B₀,A₀,A₀)
      q (A₀,B₀,B₁) = (B₀,A₀,A₁)
      q (A₀,B₁,B₀) = (B₁,A₁,A₀)
      q (A₀,B₁,B₁) = (B₁,A₀,A₀)
      q (A₁,B₀,B₀) = (B₀,A₁,A₁)
      q (A₁,B₀,B₁) = (B₁,A₀,A₁)
      q (A₁,B₁,B₀) = (B₀,A₁,A₀)
      q (A₁,B₁,B₁) = (B₁,A₁,A₁)
      d0 (A₀,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₀) (B₁,A₀) = A₀
      d0 (A₀,B₀,B₀) (B₁,A₁) = A₁
      d0 (A₀,B₀,B₁) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₁) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₁) (B₁,A₀) = A₁
      d0 (A₀,B₀,B₁) (B₁,A₁) = A₀
      d0 (A₀,B₁,B₀) (B₀,A₀) = A₁
      d0 (A₀,B₁,B₀) (B₀,A₁) = A₀
      d0 (A₀,B₁,B₀) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₀) (B₁,A₁) = A₁
      d0 (A₀,B₁,B₁) (B₀,A₀) = A₀
      d0 (A₀,B₁,B₁) (B₀,A₁) = A₁
      d0 (A₀,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₁,A₀) = A₀
      d0 (A₁,B₀,B₀) (B₁,A₁) = A₁
      d0 (A₁,B₀,B₁) (B₀,A₀) = A₁
      d0 (A₁,B₀,B₁) (B₀,A₁) = A₀
      d0 (A₁,B₀,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₀,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₁,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₁,A₀) = A₁
      d0 (A₁,B₁,B₀) (B₁,A₁) = A₀
      d0 (A₁,B₁,B₁) (B₀,A₀) = A₀
      d0 (A₁,B₁,B₁) (B₀,A₁) = A₁
      d0 (A₁,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₁,B₁) (B₁,A₁) = A₁
      d1 (A₀,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₀,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₁) (B₀,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₁,A₀) = B₀
      d1 (A₀,B₀,B₁) (B₁,A₁) = B₁
      d1 (A₀,B₁,B₀) (B₀,A₀) = B₁
      d1 (A₀,B₁,B₀) (B₀,A₁) = B₀
      d1 (A₀,B₁,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₀) (B₁,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₁,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₁,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₁) (B₀,A₀) = B₀
      d1 (A₁,B₀,B₁) (B₀,A₁) = B₁
      d1 (A₁,B₀,B₁) (B₁,A₀) = B₀
      d1 (A₁,B₀,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₀) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₀) (B₁,A₀) = B₁
      d1 (A₁,B₁,B₀) (B₁,A₁) = B₀
      d1 (A₁,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₁,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₁,B₁,B₁) (B₁,A₁) = B₁
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))
Dist #2
  let q (A₀,B₀,B₀) = (B₀,A₀,A₁)
      q (A₀,B₀,B₁) = (B₀,A₀,A₀)
      q (A₀,B₁,B₀) = (B₁,A₀,A₀)
      q (A₀,B₁,B₁) = (B₁,A₁,A₀)
      q (A₁,B₀,B₀) = (B₀,A₁,A₀)
      q (A₁,B₀,B₁) = (B₁,A₁,A₁)
      q (A₁,B₁,B₀) = (B₀,A₁,A₁)
      q (A₁,B₁,B₁) = (B₁,A₀,A₁)
      d0 (A₀,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₀) (B₁,A₀) = A₁
      d0 (A₀,B₀,B₀) (B₁,A₁) = A₀
      d0 (A₀,B₀,B₁) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₁) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₁) (B₁,A₀) = A₀
      d0 (A₀,B₀,B₁) (B₁,A₁) = A₁
      d0 (A₀,B₁,B₀) (B₀,A₀) = A₀
      d0 (A₀,B₁,B₀) (B₀,A₁) = A₁
      d0 (A₀,B₁,B₀) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₀) (B₁,A₁) = A₁
      d0 (A₀,B₁,B₁) (B₀,A₀) = A₁
      d0 (A₀,B₁,B₁) (B₀,A₁) = A₀
      d0 (A₀,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₁,A₀) = A₁
      d0 (A₁,B₀,B₀) (B₁,A₁) = A₀
      d0 (A₁,B₀,B₁) (B₀,A₀) = A₀
      d0 (A₁,B₀,B₁) (B₀,A₁) = A₁
      d0 (A₁,B₀,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₀,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₁,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₁,A₀) = A₀
      d0 (A₁,B₁,B₀) (B₁,A₁) = A₁
      d0 (A₁,B₁,B₁) (B₀,A₀) = A₁
      d0 (A₁,B₁,B₁) (B₀,A₁) = A₀
      d0 (A₁,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₁,B₁) (B₁,A₁) = A₁
      d1 (A₀,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₀,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₁) (B₀,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₁,A₀) = B₁
      d1 (A₀,B₀,B₁) (B₁,A₁) = B₀
      d1 (A₀,B₁,B₀) (B₀,A₀) = B₀
      d1 (A₀,B₁,B₀) (B₀,A₁) = B₁
      d1 (A₀,B₁,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₀) (B₁,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₁,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₁,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₁) (B₀,A₀) = B₁
      d1 (A₁,B₀,B₁) (B₀,A₁) = B₀
      d1 (A₁,B₀,B₁) (B₁,A₀) = B₀
      d1 (A₁,B₀,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₀) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₀) (B₁,A₀) = B₀
      d1 (A₁,B₁,B₀) (B₁,A₁) = B₁
      d1 (A₁,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₁,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₁,B₁,B₁) (B₁,A₁) = B₁
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))
Dist #3
  let q (A₀,B₀,B₀) = (B₀,A₀,A₁)
      q (A₀,B₀,B₁) = (B₀,A₀,A₁)
      q (A₀,B₁,B₀) = (B₁,A₁,A₀)
      q (A₀,B₁,B₁) = (B₁,A₁,A₀)
      q (A₁,B₀,B₀) = (B₀,A₁,A₀)
      q (A₁,B₀,B₁) = (B₁,A₀,A₁)
      q (A₁,B₁,B₀) = (B₀,A₁,A₀)
      q (A₁,B₁,B₁) = (B₁,A₀,A₁)
      d0 (A₀,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₀) (B₁,A₀) = A₁
      d0 (A₀,B₀,B₀) (B₁,A₁) = A₀
      d0 (A₀,B₀,B₁) (B₀,A₀) = A₀
      d0 (A₀,B₀,B₁) (B₀,A₁) = A₁
      d0 (A₀,B₀,B₁) (B₁,A₀) = A₁
      d0 (A₀,B₀,B₁) (B₁,A₁) = A₀
      d0 (A₀,B₁,B₀) (B₀,A₀) = A₁
      d0 (A₀,B₁,B₀) (B₀,A₁) = A₀
      d0 (A₀,B₁,B₀) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₀) (B₁,A₁) = A₁
      d0 (A₀,B₁,B₁) (B₀,A₀) = A₁
      d0 (A₀,B₁,B₁) (B₀,A₁) = A₀
      d0 (A₀,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₀,B₁,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₀,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₀,B₀) (B₁,A₀) = A₁
      d0 (A₁,B₀,B₀) (B₁,A₁) = A₀
      d0 (A₁,B₀,B₁) (B₀,A₀) = A₁
      d0 (A₁,B₀,B₁) (B₀,A₁) = A₀
      d0 (A₁,B₀,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₀,B₁) (B₁,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₀,A₀) = A₀
      d0 (A₁,B₁,B₀) (B₀,A₁) = A₁
      d0 (A₁,B₁,B₀) (B₁,A₀) = A₁
      d0 (A₁,B₁,B₀) (B₁,A₁) = A₀
      d0 (A₁,B₁,B₁) (B₀,A₀) = A₁
      d0 (A₁,B₁,B₁) (B₀,A₁) = A₀
      d0 (A₁,B₁,B₁) (B₁,A₀) = A₀
      d0 (A₁,B₁,B₁) (B₁,A₁) = A₁
      d1 (A₀,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₀,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₀,B₁) (B₀,A₁) = B₁
      d1 (A₀,B₀,B₁) (B₁,A₀) = B₀
      d1 (A₀,B₀,B₁) (B₁,A₁) = B₁
      d1 (A₀,B₁,B₀) (B₀,A₀) = B₁
      d1 (A₀,B₁,B₀) (B₀,A₁) = B₀
      d1 (A₀,B₁,B₀) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₀) (B₁,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₀,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₀,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₀,B₁,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₀) (B₀,A₀) = B₀
      d1 (A₁,B₀,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₀,B₀) (B₁,A₀) = B₁
      d1 (A₁,B₀,B₀) (B₁,A₁) = B₁
      d1 (A₁,B₀,B₁) (B₀,A₀) = B₀
      d1 (A₁,B₀,B₁) (B₀,A₁) = B₁
      d1 (A₁,B₀,B₁) (B₁,A₀) = B₀
      d1 (A₁,B₀,B₁) (B₁,A₁) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₀) = B₁
      d1 (A₁,B₁,B₀) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₀) (B₁,A₀) = B₁
      d1 (A₁,B₁,B₀) (B₁,A₁) = B₀
      d1 (A₁,B₁,B₁) (B₀,A₀) = B₀
      d1 (A₁,B₁,B₁) (B₀,A₁) = B₀
      d1 (A₁,B₁,B₁) (B₁,A₀) = B₁
      d1 (A₁,B₁,B₁) (B₁,A₁) = B₁
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))

-}

printIsoTable :: IO ()
printIsoTable = mapM_ (putStrLn . List.intercalate "|" . map toSymb) isoTable
  where
    toSymb b = if b then "==" else "  "

{- Output:

==|  |  |  
  |==|  |  
  |  |==|  
  |  |  |==

Interpretation:
  The generated distributed laws are not "isomorphic" each other

-}

prettyPrintDistLens :: DistLens A B -> [String]
prettyPrintDistLens l =
  pprLetIn (pprFn "q" q ++ pprFn2 "d0" d0 ++ pprFn2 "d1" d1) [ "Lens $ \\c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))" ]
  where
    q :: (A,B,B) -> (B,A,A)
    q = viewShape . coerce . fst . unLens l . coerce . reviewShape 
    
    d0 :: (A,B,B) -> (B,A) -> A
    d0 = fmap fst . snd . unLens l . coerce . reviewShape

    d1 :: (A,B,B) -> (B,A) -> B
    d1 = fmap snd . snd . unLens l . coerce . reviewShape

    indent = ("    " ++)
    pprLetIn _ [] = error "empty let-body?"
    pprLetIn [] _ = error "empty let-defs?"
    pprLetIn (firstDefLine : letLines) (firstBodyLine : inLines) =
      ["let " ++ firstDefLine]
       ++ map indent letLines
       ++ [ "in  " ++ firstBodyLine ]
       ++ map indent inLines

pprFn :: (Finitary a, Show a, Show b) => String -> (a -> b) -> [String]
pprFn fnName fn =
  [ showsUnaryWith showsPrec fnName 0 a . equal . showsPrec 0 (fn a) $ "" | a <- inhabitants ]
  where
    equal = (" = " ++) 

pprFn2 :: (Finitary a, Show a, Finitary b, Show b, Show c) => String -> (a -> b -> c) -> [String]
pprFn2 fnName fn = 
  [ showsBinaryWith showsPrec showsPrec fnName 0 a b . equal . showsPrec 0 (fn a b) $ ""
    | a <- inhabitants,
      b <- inhabitants ]
  where
    equal = (" = " ++) 

viewShape :: C a Bool b -> (a,b,b)
viewShape (C a f) = (a, f False, f True)

reviewShape :: (a,b,b) -> C a Bool b
reviewShape (a, b0, b1) = C a $ \bit -> if bit then b1 else b0

-- | Comonad automorphism
--
-- Every comonad automorphism of a store comonad @C S S@
-- come from an automorphism @(σ :: S -> S)@, as
-- @mapPos σ . mapPort σ⁻¹@
--
-- There's only one automorphism @Bool -> Bool@ that isn't @id@: @not@.
comonadAuto :: forall x. C Bool Bool x -> C Bool Bool x
comonadAuto = mapPos not . mapPort not

translate :: DistLens A B -> [DistLens A B]
translate l =
    [ distToLens (actB gB . fmap (actA gA) . dist . fmap (actB (inv gB)) . actA (inv gA))
      | (gA, gB) <- actions ]
  where
    dist :: Dist A B
    dist = distFromLens l

    actions = [ (gA, gB) | gA <- [False, True], gB <- [False, True], gA || gB ]
    inv = id

    actA :: forall x. Bool -> C A A x -> C A A x
    actA b = if b then coerce (comonadAuto @x) else id

    actB :: forall x. Bool -> C B B x -> C B B x
    actB = coerce (actA @x)

isoTable :: [[Bool]]
isoTable = [[ isIso i j | j <- [0..n-1]] | i <- [0 .. n-1]]
  where
    n = length generatedData
    revMap = Map.fromList (zip generatedData [0..])
    isoList = do
      (encLens, i) <- Map.toList revMap
      let lens = decodeLens encLens
      otherLens <- translate lens
      let encOtherLens = encodeLens otherLens
      case Map.lookup encOtherLens revMap of
        Nothing -> error "what!?"
        Just j -> pure (i,j)
    isoRelation = Set.fromList isoList
    isIso i j = i == j || (i,j) `Set.member` isoRelation
