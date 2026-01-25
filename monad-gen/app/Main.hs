{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Main (main) where

import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import System.Directory (createDirectoryIfMissing)

import Control.Monad (guard)
import Data.Bifunctor (Bifunctor(..))
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

import Data.Fin
import Targets
import Util ( writeFile' )
import Data.FunctorShape
import ApplicativeGen (
  ApplicativeDict(..),
  makeApplicativeDict,
  ApplicativeData,
  genApplicativeDataFrom, serializeApplicativeDataList)

import Options.Applicative
import Data.List (intercalate)
import GHC.Generics ((:.:))

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
  -> MonadGenType
  -> (String -> IO ())
  -> IO [(String, MonadData f)]
monadGen applicatives genType println = do
  let monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      
      gen = case genType of
        MonadGenV1 -> genFromApplicativeModuloIso
        MonadGenV2 -> \apDict -> MonadGen2.moduloIso apDict $ MonadGen2.genFromApplicative apDict
        MonadGenV2Cached -> case MonadGen2.prepareGenFromApplicative of
          Nothing -> const []
          Just genPrepared -> \apDict -> MonadGen2.moduloIso apDict (genPrepared apDict)
      
      monads :: [ (String, MonadData f) ]
      monads = do
        (apName, apData) <- applicatives
        monadData <- gen (makeApplicativeDict apData)
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
  -> MonadGenType
  -> (String -> IO ())
  -> IO [(String, Set.Set (MonadData f))]
monadGenGroup applicatives genType println = do
  let monadNames = [ "Monad_" ++ show i | i <- [ 1 :: Int ..] ]
      gen = case genType of
        MonadGenV1 -> genFromApplicativeIsoGroups
        MonadGenV2 -> \apDict -> MonadGen2.groupsIso apDict $ MonadGen2.genFromApplicative apDict
        MonadGenV2Cached -> case MonadGen2.prepareGenFromApplicative of
          Nothing -> const []
          Just genPrepared -> \apDict -> MonadGen2.groupsIso apDict (genPrepared apDict)
      monads :: [ (String, Set.Set (MonadData f)) ]
      monads = do
        (apName, apData) <- applicatives
        monadDataGroup <- gen (makeApplicativeDict apData)
        pure (apName, monadDataGroup)
  for_ (zip monadNames monads) $ \(monadName, (apName, monadDataGroup)) -> do
    let dicts = makeMonadDict <$> Set.toList monadDataGroup
        indent = ("  " <>)
    println "IsomorphismClass {"
    for_ dicts $ \dict -> do
      mapM_ (println . indent) $ prettyMonadDict monadName apName dict
      validateMonadDict dict
    println "}"
  pure monads

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

generateAll
  :: (PTraversable f, forall a. Show a => Show (f a))
  => String -> Proxy f -> Option -> IO ()
generateAll displayName name opt = do
  createDirectoryIfMissing True outDir -- `mkdir -p $outDir`
  
  monoids <- writeFile' (outDir ++ "/monoid.txt") $ monoidGen name
  writeFile (outDir ++ "/monoid_data") $ unlines $ serializeMonoidDataList lengthShape (snd <$> monoids)
  
  applicatives <- writeFile' (outDir ++ "/applicative.txt") $ applicativeGen monoids
  writeFile (outDir ++ "/applicative_data") $ unlines $ serializeApplicativeDataList (snd <$> applicatives)
  
  monads <-
    if monadGroups
      then do monad_groups <- writeFile' (outDir ++ "/monad_group.txt") $ monadGenGroup applicatives monadGenMethod
              pure (second Set.findMin <$> monad_groups)
      else writeFile' (outDir ++ "/monad.txt") $ monadGen applicatives monadGenMethod
  writeFile (outDir ++ "/monad_data") $ unlines $ serializeMonadDataList (snd <$> monads)

  where
    outDir = optOutputDirectoryRoot opt ++ "/" ++ displayName
    monadGenMethod = optMonadGen opt
    monadGroups = optMonadGroups opt

targetNamed :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => String -> Proxy f -> (String, Option -> IO ())
targetNamed displayName name = (displayName, generateAll displayName name)

target :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> (String, Option -> IO ())
target name = targetNamed (show (someTypeRep name)) name

targets :: Map.Map String (Option -> IO ())
targets = Map.fromList
  [
    targetNamed @Maybe "wellknown/Maybe" Proxy,
    targetNamed @V2 "wellknown/V2" Proxy,
    targetNamed @V3 "wellknown/V3" Proxy,
    targetNamed @((,) (Fin 2)) "wellknown/Writer2" Proxy,
    targetNamed @((,) (Fin 3)) "wellknown/Writer3" Proxy,

    target @F Proxy,
    target @G Proxy,
    target @H Proxy,
    target @I Proxy,
    target @T_013 Proxy,
    target @T_112 Proxy,

    targetNamed @(EW (Fin 1) (Fin 2)) "E1W2" Proxy,
    targetNamed @(EW (Fin 2) (Fin 2)) "E2W2" Proxy,

    targetNamed @(St (Fin 2) V2) "St22" Proxy,
    targetNamed @(St (Fin 3) V2) "St32" Proxy,
    targetNamed @(St (Fin 4) V2) "St42" Proxy,

    targetNamed @(V2 :.: Maybe) "complex/V2Maybe" Proxy
  ]

data Option = Option {
    optOutputDirectoryRoot :: FilePath,
    optMonadGen :: MonadGenType,
    optMonadGroups :: Bool,
    optTargets :: Set.Set String
  }

data MonadGenType = MonadGenV1 | MonadGenV2 | MonadGenV2Cached
  deriving (Show, Read, Eq)

data TargetSpec = TargetAll | IncludeOne String | ExcludeOne String

optParser :: Set.Set String -> ParserInfo Option
optParser targetNames =
  info
    (parserBody <**> helper)
    (fullDesc
       <> progDesc "Enumerates all possible Monad instances"
       <> footer descTargets)
  where
    parserBody = Option <$> oOutDir <*> oMonadGen <*> oMonadGroups <*> oTargets
    oOutDir = strOption $
      value "output" <> showDefault
        <> long "outdir" <> short 'o'
        <> metavar "PATH_TO_DIR" <> help "Output directory"
    
    oMonadGen =
          flag' MonadGenV1 (long "v1" <> help "Use old solver")
      <|> flag' MonadGenV2 (long "v2" <> help "Use new solver")
      <|> flag' MonadGenV2Cached (long "v2-cached" <> help "Use new solver (cached)")
      <|> pure MonadGenV1
    oMonadGroups = switch (long "groups" <> help "During Monad generation, output isomorphism classes too")
    
    oTargets = parserOptionGroup "Target specifications" $
      aggregateTargets <$> some (oAll <|> oSingleTarget <|> oExcludeSingleTarget)

    oAll = flag' TargetAll (long "all" <> short 'a' <> help "Include all targets")
    readTargetName = maybeReader (\s -> s <$ guard (Set.member s targetNames))
    oSingleTarget = IncludeOne <$>
      argument readTargetName (metavar "TARGET" <> help "Include a target")
    oExcludeSingleTarget = ExcludeOne <$>
      option readTargetName
        (short 'x' <> metavar "TARGET" <> help "Exclude a target")

    aggregateTargets = foldl' step Set.empty
      where
        step s opt = case opt of
          TargetAll -> targetNames
          IncludeOne t -> Set.insert t s
          ExcludeOne t -> Set.delete t s
    
    descTargets = unlines
      [ "\tTARGET:",
        "\t    " ++ intercalate "," (show <$> Set.toList targetNames) ]

main :: IO ()
main = do
  opt <- execParser $ optParser (Map.keysSet targets)
  let runTarget name = Map.findWithDefault (const (fail "!?")) name targets opt
  if null (optTargets opt)
    then hPutStrLn stderr "All targets are excluded" >> exitFailure
    else mapM_ runTarget (optTargets opt)
