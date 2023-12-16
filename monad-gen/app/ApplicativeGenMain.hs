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
import MonoidGen
import ApplicativeGen

import Data.Two
import Targets
import Util
import Data.FunctorShape

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
    PTraversable f
  ) =>
  Proxy f ->
  (String -> IO ()) ->
  IO ()
applicativeGen proxy println = do
  monoids <- monoidGen proxy println
  let applicativeNames = [ "A_" ++ show i | i <- [ 1 :: Int ..] ]
      applicatives :: [ (String, ApplicativeData f) ]
      applicatives = do
        (monoidName, monData) <- monoids
        applicativeData <- genApplicativeDataFrom monData
        pure (monoidName, applicativeData)
  for_ (zip applicativeNames applicatives) $ \(applicativeName, (monoidName, applicativeData)) -> do
    let dict = makeApplicativeDict applicativeData
    mapM_ println $ prettyApplicativeDict applicativeName monoidName dict

dieWithErrors :: [String] -> IO a
dieWithErrors errs = mapM_ (hPutStrLn stderr) errs >> exitFailure

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

main :: IO ()
main = do
  writeFile' "output/applicative/Writer.txt" $ applicativeGen @((,) Two) Proxy
  writeFile' "output/applicative/Writer3.txt" $ applicativeGen @((,) N3) Proxy
  writeFile' "output/applicative/Maybe.txt" $ applicativeGen @Maybe Proxy

  writeFile' "output/applicative/F.txt" $ applicativeGen @F Proxy
  writeFile' "output/applicative/G.txt" $ applicativeGen @G Proxy
  writeFile' "output/applicative/H.txt" $ applicativeGen @H Proxy
  writeFile' "output/applicative/I.txt" $ applicativeGen @I Proxy
  writeFile' "output/applicative/J.txt" $ applicativeGen @J Proxy
  writeFile' "output/applicative/T.txt" $ applicativeGen @T Proxy
  writeFile' "output/applicative/U.txt" $ applicativeGen @U Proxy
  writeFile' "output/applicative/V.txt" $ applicativeGen @V Proxy
  -- writeFile' "output/Y.txt" $ monadGen @Y Proxy
