{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Data.Foldable
import qualified Data.LazyVec as Vec
import Data.PTraversable
import Data.PTraversable.Extra
import Data.Proxy
import MonadLaws
import MonoidGen
import MonadGen
import Isomorphism (makePositionIsoFactors)

import Data.Two
import Targets
import Util

------------------------
-- Tests

forAll :: (Foldable t) => t a -> (a -> Bool) -> Bool
forAll = flip all

monadGen ::
  forall f.
  ( forall a. (Ord a) => Ord (f a),
    forall a. (Show a) => Show (f a),
    PTraversable f
  ) =>
  Proxy f ->
  (String -> IO ()) ->
  IO ()
monadGen _ println = do
  let monoidNames = [ "M_" ++ show i | i <- [ 1 :: Int .. ] ]
      monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      monoids = zip monoidNames genMonoids
      monads = do
        (monoidName, monData) <- monoids
        monadData <- uniqueByIso (concat makePositionIsoFactors) $ genFromMonoid (makeMonoidDict monData)
        pure (monoidName, monadData)
  for_ monoids $ \(monoidName, monData) -> mapM_ println (prettyMonoidData monoidName monData)
  for_ (zip monadNames monads) docResult
  where
    skolemCache :: Vec (f Int)
    skolemCache = cache skolem

    skolem2Cache :: Vec (f (f Int))
    skolem2Cache = cache skolem2

    skolem3Cache :: Vec (f (f (f Int)))
    skolem3Cache = cache skolem3

    validate :: MonadDict f -> IO ()
    validate MonadDict{ _monadPure = pure', _monadJoin = join' } =
      if and allLaws
        then return ()
        else fail $ "[leftUnit, rightUnit, assoc] = " ++ show allLaws
      where
        leftUnitLaw = forAll skolemCache $ checkLeftUnit pure' join'
        rightUnitLaw = forAll skolemCache $ checkRightUnit pure' join'
        assocLaw = forAll skolem3Cache $ checkAssoc join'
        allLaws = [leftUnitLaw, rightUnitLaw, assocLaw]

    joinArgsCache :: Vec String
    joinArgsCache = cache $ fmap pad strs
      where
        showLen x = let s = show x in (length s, s)
        strs = cache $ showLen <$> skolem2Cache
        maxLen = maximum $ fmap fst strs
        pad (n, s) = "join $ " ++ s ++ replicate (maxLen - n) ' ' ++ " = "

    docResult (monadName, (monoidName, monadData)) = do
        validate dict
        println $ monadName ++ " = Monad{"
        println $ indent <> "baseMonoid = " ++ monoidName
        println $ indent <> "pure 0 = " <> show (_monadPure dict (0 :: Int))
        let docLine s ffx = indent <> s <> show (_monadJoin dict ffx)
        mapM_ println $
          Vec.zipWith docLine joinArgsCache skolem2Cache
        println "}\n"
      where
        indent = "    "
        dict = makeMonadDict monadData

main :: IO ()
main = do
  writeFile' "output/Writer.txt" $ monadGen @((,) Two) Proxy
  writeFile' "output/Writer3.txt" $ monadGen @((,) N3) Proxy
  writeFile' "output/Maybe.txt" $ monadGen @Maybe Proxy

  writeFile' "output/F.txt" $ monadGen @F Proxy
  writeFile' "output/G.txt" $ monadGen @G Proxy
  writeFile' "output/H.txt" $ monadGen @H Proxy
  writeFile' "output/I.txt" $ monadGen @I Proxy
  writeFile' "output/J.txt" $ monadGen @J Proxy
  writeFile' "output/T.txt" $ monadGen @T Proxy
  writeFile' "output/U.txt" $ monadGen @U Proxy
  writeFile' "output/V.txt" $ monadGen @V Proxy
  --writeFile' "output/Y.txt" $ monadGen @Y Proxy
