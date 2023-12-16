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
import System.Directory (createDirectoryIfMissing)

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
import Util ( writeFile' )
import Data.FunctorShape
import ApplicativeGen (
  ApplicativeDict(..),
  makeApplicativeDict,
  ApplicativeData,
  genApplicativeDataFrom)

------------------------
-- Tests

monoidGen ::
  forall f.
  ( forall a. (Show a) => Show (f a),
    PTraversable f
  ) =>
  Proxy f ->
  (String -> IO ()) ->
  IO [ (String, MonoidData (Shape f)) ]
monoidGen _ println = do
  let monoidNames = [ "M_" ++ show i | i <- [ 1 :: Int .. ] ]
      monoids = zip monoidNames (genMonoidsWithSig (length . unShape))
  for_ monoids $ \(monoidName, monData) -> mapM_ println (prettyMonoidData monoidName monData)
  pure monoids

applicativeGen ::
  forall f.
  ( forall a. (Show a) => Show (f a),
    PTraversable f )
  => [ (String, MonoidData (Shape f)) ]
  -> (String -> IO ())
  -> IO [ (String, ApplicativeData f) ]
applicativeGen monoids println = do
  let applicativeNames = [ "A_" ++ show i | i <- [ 1 :: Int ..] ]
      applicatives :: [ (String, ApplicativeData f) ]
      applicatives = do
        (monoidName, monData) <- monoids
        applicativeData <- genApplicativeDataFrom monData
        pure (monoidName, applicativeData)
  for_ (zip applicativeNames applicatives) $ \(applicativeName, (monoidName, applicativeData)) -> do
    let dict = makeApplicativeDict applicativeData
    mapM_ println $ prettyApplicativeDict applicativeName monoidName dict
  pure (zip applicativeNames (snd <$> applicatives))

prettyApplicativeDict :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => String -> String -> ApplicativeDict f -> [String]
prettyApplicativeDict = docResult
  where
    skolemCache :: [f Int]
    skolemCache = toList skolem
    
    lhsCache :: [String]
    lhsCache = pad <$> strs
      where
        showLen x y =
          let s = "(" ++ show x ++ ") (" ++ show y ++ ")"
          in (length s, s)
        strs = showLen <$> skolemCache <*> skolemCache
        maxLen = maximum $ (0 : fmap fst strs)
        pad (n, s) = "liftA2 (,) " ++ s ++ replicate (maxLen - n) ' ' ++ " = "
    
    indent = "  "
    
    docResult monadName monoidName dict =
        [ monadName <> " = Applicative{" ] ++
        map (indent <>) (
          [ "baseMonoid = " ++ monoidName,
            "pure 0 = " <> show (_applicativePure dict (0 :: Int)) ] ++
          zipWith (<>) lhsCache (show <$> rhs)
        ) ++
        ["}"]
        where
          rhs = _applicativeLiftA2 dict (,) <$> skolemCache <*> skolemCache

monadGen
  :: forall f.
    ( forall a. (Show a) => Show (f a), PTraversable f)
  => [ (String, ApplicativeData f) ]
  -> (String -> IO ())
  -> IO ()
monadGen applicatives println = do
  let monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      monads :: [ (String, MonadData f) ]
      monads = do
        (apName, apData) <- applicatives
        monadData <- uniqueByIso (concat makePositionIsoFactors) $ genFromApplicative (makeApplicativeDict apData)
        pure (apName, monadData)
  for_ (zip monadNames monads) $ \(monadName, (apName, monadData)) -> do
    let dict = makeMonadDict monadData
    validateMonadDict dict
    mapM_ println $ prettyMonadDict monadName apName dict

monadGenGroup
  :: forall f.
    ( forall a. (Show a) => Show (f a), PTraversable f)
  => [ (String, ApplicativeData f) ]
  -> (String -> IO ())
  -> IO ()
monadGenGroup applicatives println = do
  let monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      monads :: [ (String, [MonadData f]) ]
      monads = do
        (apName, apData) <- applicatives
        monadDataGroup <- groupByIso (concat makePositionIsoFactors) $ genFromApplicative (makeApplicativeDict apData)
        pure (apName, toList monadDataGroup)
  for_ (zip monadNames monads) $ \(monadName, (apName, monadDataGroup)) -> do
    let dicts = makeMonadDict <$> monadDataGroup
    mapM_ validateMonadDict dicts
    let
      prettyGroup = ["IsomorphismClass {"]
        ++ map ("  " <>) (concatMap (prettyMonadDict monadName apName) dicts)
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
    skolem2Cache = toList skolem2
    
    joinArgsCache :: [String]
    joinArgsCache = pad <$> strs
      where
        showLen x = let s = show x in (length s, s)
        strs = showLen <$> skolem2Cache
        maxLen = maximum (0 : fmap fst strs)
        pad (n, s) = "join $ " ++ s ++ replicate (maxLen - n) ' ' ++ " = "
    
    indent = "  "
    
    docResult monadName apName dict =
        [ monadName <> " = Monad{" ] ++
        map (indent <>) (
          [ "baseApplicative = " ++ apName,
            "pure 0 = " <> show (_monadPure dict (0 :: Int)) ] ++
          zipWith (<>) joinArgsCache (show . _monadJoin dict <$> skolem2Cache)
        ) ++
        ["}"]

generateAllToDir
  :: (PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> FilePath -> IO ()
generateAllToDir name outDir = do
  createDirectoryIfMissing True outDir -- `mkdir -p $outDir`
  monoids <- writeFile' (outDir ++ "/monoid.txt") $ monoidGen name
  applicatives <- writeFile' (outDir ++ "/applicative.txt") $ applicativeGen monoids
  writeFile' (outDir ++ "/monad.txt") $ monadGen applicatives

generateAllToDir_andGroups
  :: (PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> FilePath -> IO ()
generateAllToDir_andGroups name outDir = do
  createDirectoryIfMissing True outDir -- `mkdir -p $outDir`
  monoids <- writeFile' (outDir ++ "/monoid.txt") $ monoidGen name
  applicatives <- writeFile' (outDir ++ "/applicative.txt") $ applicativeGen monoids
  writeFile' (outDir ++ "/monad.txt") $ monadGen applicatives
  writeFile' (outDir ++ "/monad_group.txt") $ monadGenGroup applicatives

main :: IO ()
main = do
  generateAllToDir @Maybe Proxy "output/Maybe"
  generateAllToDir @((,) Two) Proxy "output/Writer"
  generateAllToDir @((,) N3) Proxy "output/Writer3"

  generateAllToDir @F Proxy "output/F"
  generateAllToDir @G Proxy "output/G"
  generateAllToDir @H Proxy "output/H"
  generateAllToDir @I Proxy "output/I"
  generateAllToDir @J Proxy "output/J"
  generateAllToDir_andGroups @T Proxy "output/T"
  generateAllToDir_andGroups @U Proxy "output/U"
  generateAllToDir @V Proxy "output/V"
  -- generateAllToDir @Y Proxy "output/Y"
