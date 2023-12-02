{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Data.Foldable
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

monoidGen ::
  forall f.
  ( forall a. (Show a) => Show (f a),
    PTraversable f
  ) =>
  Proxy f ->
  (String -> IO ()) ->
  IO [ (String, MonoidData f) ]
monoidGen _ println = do
  let monoidNames = [ "M_" ++ show i | i <- [ 1 :: Int .. ] ]
      monoids = zip monoidNames genMonoids
  for_ monoids $ \(monoidName, monData) -> mapM_ println (prettyMonoidData monoidName monData)
  pure monoids

monadGen ::
  forall f.
  ( forall a. (Show a) => Show (f a),
    PTraversable f
  ) =>
  Proxy f ->
  (String -> IO ()) ->
  IO ()
monadGen proxy println = do
  monoids <- monoidGen proxy println
  let monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      monads :: [ (String, MonadData f) ]
      monads = do
        (monoidName, monData) <- monoids
        monadData <- uniqueByIso (concat makePositionIsoFactors) $ genFromMonoid (makeMonoidDict monData)
        pure (monoidName, monadData)
  for_ (zip monadNames monads) $ \(monadName, (monoidName, monadData)) -> do
    let dict = makeMonadDict monadData
    validateMonadDict dict
    mapM_ println $ prettyMonadDict monadName monoidName dict

monadGenGroup ::
  forall f.
  ( forall a. (Show a) => Show (f a),
    PTraversable f
  ) =>
  Proxy f ->
  (String -> IO ()) ->
  IO ()
monadGenGroup proxy println = do
  monoids <- monoidGen proxy println
  let monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      monads :: [ (String, [MonadData f]) ]
      monads = do
        (monoidName, monData) <- monoids
        monadDataGroup <- groupByIso (concat makePositionIsoFactors) $ genFromMonoid (makeMonoidDict monData)
        pure (monoidName, toList monadDataGroup)
  for_ (zip monadNames monads) $ \(monadName, (monoidName, monadDataGroup)) -> do
    let dicts = makeMonadDict <$> monadDataGroup
    mapM_ validateMonadDict dicts
    let
      prettyGroup = ["IsomorphismClass {"]
        ++ map ("  " <>) (concatMap (prettyMonadDict monadName monoidName) dicts)
        ++ ["}"]
    mapM_ println prettyGroup

validateMonadDict :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => MonadDict f -> IO ()
validateMonadDict MonadDict{ _monadPure = pure', _monadJoin = join' }
   = if null allFails
       then pure ()
       else dieWithErrors allFails
  where
    skolemCache :: [f Int]
    skolemCache = toList skolem

    skolem3Cache :: [f (f (f Int))]
    skolem3Cache = toList skolem3
 
    leftUnitFails = 
      [ "leftUnit " ++ show fx | fx <- skolemCache, not (checkLeftUnit pure' join' fx) ]
    rightUnitFails = 
      [ "rightUnit " ++ show fx | fx <- skolemCache, not (checkRightUnit pure' join' fx) ]
    assocFails = 
      [ "assoc " ++ show fffx | fffx <- skolem3Cache, not (checkAssoc join' fffx) ]

    allFails = leftUnitFails ++ rightUnitFails ++ assocFails

dieWithErrors :: [String] -> IO a
dieWithErrors errs = mapM_ (hPutStrLn stderr) errs >> exitFailure

prettyMonadDict :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => String -> String -> MonadDict f -> [String]
prettyMonadDict = docResult
  where
    skolem2Cache :: [f (f Int)]
    skolem2Cache = toList $ skolem2
    
    joinArgsCache :: [String]
    joinArgsCache = pad <$> strs
      where
        showLen x = let s = show x in (length s, s)
        strs = showLen <$> skolem2Cache
        maxLen = maximum $ (0 : fmap fst strs)
        pad (n, s) = "join $ " ++ s ++ replicate (maxLen - n) ' ' ++ " = "
    
    indent = "  "
    
    docResult monadName monoidName dict =
        [ monadName <> " = Monad{" ] ++
        map (indent <>) (
          [ "baseMonoid = " ++ monoidName,
            "pure 0 = " <> show (_monadPure dict (0 :: Int)) ] ++
          zipWith (<>) joinArgsCache (show . _monadJoin dict <$> skolem2Cache)
        ) ++
        ["}"]

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
  writeFile' "output/Tgroups.txt" $ monadGenGroup @T Proxy
  writeFile' "output/U.txt" $ monadGen @U Proxy
  writeFile' "output/Ugroups.txt" $ monadGenGroup @U Proxy
  writeFile' "output/V.txt" $ monadGen @V Proxy
  writeFile' "output/Y.txt" $ monadGen @Y Proxy
