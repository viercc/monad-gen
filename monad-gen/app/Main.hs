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
import Data.Either (partitionEithers)

import Data.Foldable
import Data.PTraversable
import Data.PTraversable.Extra
import Data.Proxy
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Type.Reflection

import qualified ApplicativeLaws as Ap
import MonadLaws
import MonoidGen
import MonadGen
import qualified MonadGen2

import Data.Two
import Targets
import Util ( writeFile' )
import Data.FunctorShape
import ApplicativeGen (
  ApplicativeDict(..),
  makeApplicativeDict,
  ApplicativeData,
  genApplicativeDataFrom, serializeApplicativeDataList)
import System.Environment (getArgs)

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
      monoids = zip monoidNames (genMonoidsWithSig lengthShape)
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
    validateApplicativeDict dict
  pure (zip applicativeNames (snd <$> applicatives))

validateApplicativeDict :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => ApplicativeDict f -> IO ()
validateApplicativeDict ApplicativeDict{ _applicativePure = pure', _applicativeLiftA2 = liftA2' }
   = if null allFails
       then pure ()
       else dieWithErrors allFails
  where
    skolemCache :: [f Int]
    skolemCache = toList skolem

    leftUnitFails = 
      [ "leftUnit " ++ show fx | fx <- skolemCache, not (Ap.checkLeftUnit pure' liftA2' fx) ]
    rightUnitFails = 
      [ "rightUnit " ++ show fx | fx <- skolemCache, not (Ap.checkRightUnit pure' liftA2' fx) ]
    assocFails = 
      [ "assoc " ++ show (fx, fy, fz)
        | fx <- skolemCache,
          fy <- skolemCache,
          fz <- skolemCache,
          not (Ap.checkAssoc liftA2' fx fy fz)
      ]

    allFails = leftUnitFails ++ rightUnitFails ++ assocFails

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
  -> Bool
  -> (String -> IO ())
  -> IO [(String, MonadData f)]
monadGen applicatives use2 println = do
  let monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      generator
        | use2      = MonadGen2.genFromApplicativeModuloIso
        | otherwise = genFromApplicativeModuloIso 
      
      monads :: [ (String, MonadData f) ]
      monads = do
        (apName, apData) <- applicatives
        monadData <- generator (makeApplicativeDict apData)
        pure (apName, monadData)
  for_ (zip monadNames monads) $ \(monadName, (apName, monadData)) -> do
    let dict = makeMonadDict monadData
    mapM_ println $ prettyMonadDict monadName apName dict
    validateMonadDict dict
  pure (zip monadNames (snd <$> monads))

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
        monadDataGroup <- genFromApplicativeIsoGroups (makeApplicativeDict apData)
        pure (apName, monadDataGroup)
  for_ (zip monadNames monads) $ \(monadName, (apName, monadDataGroup)) -> do
    let dicts = makeMonadDict <$> monadDataGroup
        indent = ("  " <>)
    println "IsomorphismClass {"
    for_ dicts $ \dict -> do
      mapM_ (println . indent) $ prettyMonadDict monadName apName dict
      validateMonadDict dict
    println "}"

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
  => Proxy f -> Bool -> FilePath -> IO ()
generateAllToDir name use2 outDir = do
  createDirectoryIfMissing True outDir -- `mkdir -p $outDir`
  
  monoids <- writeFile' (outDir ++ "/monoid.txt") $ monoidGen name
  writeFile (outDir ++ "/monoid_data") $ unlines $ serializeMonoidDataList lengthShape (snd <$> monoids)
  
  applicatives <- writeFile' (outDir ++ "/applicative.txt") $ applicativeGen monoids
  writeFile (outDir ++ "/applicative_data") $ unlines $ serializeApplicativeDataList (snd <$> applicatives)
  
  monads <- writeFile' (outDir ++ "/monad.txt") $ monadGen applicatives use2
  writeFile (outDir ++ "/monad_data") $ unlines $ serializeMonadDataList (snd <$> monads)

generateAllAndGroupsToDir
  :: (PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> FilePath -> IO ()
generateAllAndGroupsToDir name outDir = do
  createDirectoryIfMissing True outDir -- `mkdir -p $outDir`

  monoids <- writeFile' (outDir ++ "/monoid.txt") $ monoidGen name
  writeFile (outDir ++ "/monoid_data") $ unlines $ serializeMonoidDataList lengthShape (snd <$> monoids)
  
  applicatives <- writeFile' (outDir ++ "/applicative.txt") $ applicativeGen monoids
  writeFile (outDir ++ "/applicative_data") $ unlines $ serializeApplicativeDataList (snd <$> applicatives)

  monads <- writeFile' (outDir ++ "/monad.txt") $ monadGen applicatives False
  writeFile (outDir ++ "/monad_data") $ unlines $ serializeMonadDataList (snd <$> monads)

  writeFile' (outDir ++ "/monad_group.txt") $ monadGenGroup applicatives

target :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> (String, IO ())
target name = (nameStr, generateAllToDir name False ("output/" ++ nameStr))
  where
    nameStr = show (someTypeRep name)

target2 :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> (String, IO ())
target2 name = (nameStr ++ "(2)", generateAllToDir name True ("output/" ++ nameStr))
  where
    nameStr = show (someTypeRep name)

targetG :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> (String, IO ())
targetG name = (nameStr ++ "-groups", generateAllAndGroupsToDir name ("output/" ++ nameStr))
  where
    nameStr = show (someTypeRep name)

targets :: Map.Map String (IO ())
targets = Map.fromList
  [
    target @Maybe Proxy,
    target @((,) Two) Proxy,
    target @((,) N3) Proxy,

    target @F Proxy,
    target @G Proxy,
    target @H Proxy,
    target @I Proxy,
    target @I' Proxy,

    target2 @F Proxy,
    target2 @G Proxy,
    target2 @H Proxy,
    target2 @I Proxy,
    target2 @I' Proxy,

    target @J Proxy,
    target @K Proxy,
    target @L Proxy,

    target @T Proxy,
    targetG @T Proxy,

    target @U Proxy,
    target @V Proxy,
    target @X Proxy,
    target @W Proxy,
    target @Y Proxy
  ]

main :: IO ()
main = getArgs >>= \args -> case args of
  [] -> printUsage
  _ -> argsToTargetSet args >>= mapM_ runTarget
  where
    runTarget :: String -> IO ()
    runTarget name = Map.findWithDefault (fail "!?") name targets

printUsage :: IO a
printUsage = do
  putStrLn "Usage: monad-gen [TARGET]..."
  putStrLn ""
  putStrLn "\tTARGET = all | [-]<FunctorName>"
  putStrLn $ "\tFunctorName = " ++ show (Map.keys targets)
  exitFailure

argsToTargetSet :: [String] -> IO [String]
argsToTargetSet args = case partitionEithers (concatMap parseArg args) of
  (err, targetList)
    | null err -> case subtractList (partitionEithers targetList) of
        [] -> hPutStrLn stderr "No targets" >> exitFailure
        targetList' -> pure targetList'
    | otherwise -> mapM_ (\s -> hPutStrLn stderr $ "Unknown target:" ++ show s ) err >> exitFailure
  where
    parseArg arg = case arg of
      "all" -> Right . Left <$> Map.keys targets
      ('-' : negArg)
        | Map.member negArg targets -> [ Right . Right $ negArg ]
      _ | Map.member arg targets -> [ Right . Left $ arg ]
        | otherwise -> [ Left arg ]

subtractList :: Ord a => ([a], [a]) -> [a]
subtractList (xs, ys) = go (Set.fromList ys) xs
  where
    go _ [] = []
    go used (z:zs)
      | Set.member z used = go used zs
      | otherwise = z : go (Set.insert z used) zs
