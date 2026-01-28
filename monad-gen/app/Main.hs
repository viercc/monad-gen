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

import Prelude hiding (Enum)

import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr, hGetContents, IOMode (ReadMode), withFile)
import qualified System.IO.Error as IOE
import Control.Exception (catch, throwIO)
import System.Directory (createDirectoryIfMissing)

import Control.Monad (guard)
import Data.Foldable
import Data.Finitary.Enum (Enum(), enum)
import Data.PTraversable
import Data.PTraversable.Extra
import Data.Proxy
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Type.Reflection

import qualified ApplicativeLaws as Ap
import MonadLaws

import MonoidData
import MonoidGen

import ApplicativeData
import ApplicativeGen (genApplicativeDataFrom)
import MonadData
import MonadGen
import qualified MonadGen2

import Data.Fin
import Targets
import Util 
import Data.FunctorShape

import Options.Applicative
import Data.List (intercalate, sort)
import GHC.Generics ((:.:))

-- * Targets

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

targetNamed :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => String -> Proxy f -> (String, Option -> IO ())
targetNamed displayName name = (displayName, generateAll displayName name)

target :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => Proxy f -> (String, Option -> IO ())
target name = targetNamed (show (someTypeRep name)) name

-- * Options and main

data Option = Option {
    optOutputDirectoryRoot :: FilePath,
    optScheme :: GenerationScheme,
    optUseExistingFile :: Bool,
    optMonadGen :: MonadGenType,
    optTargets :: Set.Set String
  }
  deriving (Show, Eq)

data GenerationScheme =
    SchemeMon         -- Monoid only
  | SchemeMonApp      -- Monoid --> Applicative
  | SchemeMonAppMonad -- Monoid --> Applicative --> Monad
  | SchemeMonMonad    -- Monoid --> Monad
  deriving (Show, Eq)

data MonadGenType = MonadGenV1 | MonadGenV2 | MonadGenV2Cached
  deriving (Show, Read, Eq)

data TargetSpec = TargetAll | IncludeOne String | ExcludeOne String

switchRich :: String -> Bool -> Mod FlagFields Bool -> Parser Bool
switchRich longName defaultOn otherMods =
      flag' True (long longName <> otherMods)
  <|> flag' False (hidden <> long ("no-" ++ longName))
  <|> pure defaultOn

optParser :: Set.Set String -> ParserInfo Option
optParser targetNames =
  info
    (parserBody <**> helper)
    (fullDesc
       <> progDesc "Enumerates all possible Monad instances"
       <> footer descTargets)
  where
    parserBody =
      Option
        <$> oOutDir
        <*> oScheme
        <*> oUseExisting
        <*> oMonadGen
        <*> oTargets
    oOutDir = strOption $
      value "output" <> showDefault
        <> long "outdir" <> short 'o'
        <> metavar "PATH_TO_DIR" <> help "Output directory"
    
    oScheme = parserOptionGroup "Generation schemes" $
          flag' SchemeMon (long "monoid-only" <> help "Monoid only (no Applicative or Monad)")
      <|> flag' SchemeMonApp (long "monoid-app" <> help "Monoid -> Applicative (no Monad)")
      <|> flag' SchemeMonAppMonad (long "monoid-app-monad" <> help "(default) Monoid -> Applicative -> Monad")
      <|> flag' SchemeMonMonad (long "monoid-monad" <> help "Monoid -> Monad")
      <|> pure SchemeMonAppMonad

    oUseExisting =
      switchRich "use-datafile" True (help "Use existing datafile and skips generation if able (default: on)")

    oMonadGen = parserOptionGroup "Monad generation engine" $
          flag' MonadGenV1 (long "v1" <> help "(default) Use v1 solver")
      <|> flag' MonadGenV2 (long "v2" <> help "Use v2 solver")
      <|> flag' MonadGenV2Cached (long "v2-cached" <> help "Use v2 solver with cached E-Graph")
      <|> pure MonadGenV1
    
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


-- * Main logic for each target

generateAll
  :: (Typeable f, PTraversable f, forall a. Show a => Show (f a))
  => String -> Proxy f -> Option -> IO ()
generateAll displayName name opt = do
  createDirectoryIfMissing True outDir -- `mkdir -p $outDir`
  
  monoids <- progress $ monoidGenToFile name monoidFileName useExisting
  let namedMonoids = [ ("M_" ++ show i, mon) | (i,mon) <- zip [1 :: Int ..] monoids ]
  
  applicatives <- progress $ applicativeGenToFile namedMonoids applicativeFileName useExisting
  let namedApplicatives = [ ("A_" ++ show i, apData) | (i,apData) <- zip [1 :: Int ..] applicatives ]
  
  _ <- progress $ monadGenFromApplicativeToFile namedApplicatives monadFileName monadGenMethod
  pure ()

  where
    outDir = optOutputDirectoryRoot opt ++ "/" ++ displayName
    logFileName = outDir ++ "/progress_log"
    monadGenMethod = optMonadGen opt
    useExisting = optUseExistingFile opt
  
    monoidFileName = outDir ++ "/monoid_data"
    applicativeFileName = outDir ++ "/applicative_data"
    monadFileName = outDir ++ "/monad_data"
    
    progress :: Logger
    progress = statusLine $ timed $ loggedTo logFileName discard

-- * Monoid

monoidGenToFile :: forall f.
  ( Typeable f, forall a. (Show a) => Show (f a), PTraversable f)
  => Proxy f
  -> FilePath
  -> Bool
  -> (String -> IO ())
  -> IO [MonoidData (Shape f)]
monoidGenToFile name outfile readIfExist logger = do
  readResult <-
    if readIfExist
      then readMonoidData name outfile
      else pure Nothing
  case readResult of
    Nothing -> do
      monoids <- monoidGen name logger
      writeFile outfile $ unlines $ serializeMonoidDataList lengthShape monoids
      pure monoids
    Just monoids -> pure monoids

monoidGen :: forall f.
  ( Typeable f, forall a. (Show a) => Show (f a), PTraversable f)
  => Proxy f
  -> (String -> IO ())
  -> IO [MonoidData (Shape f)]
monoidGen name progress = do
  let typename = show (someTypeRep name)
      monoids = genMonoidsWithSig lengthShape
      counter = [1 :: Int ..]
  for_ (zip counter monoids) $ \(i, mon) -> do
    validateMonoidData mon
    progress ("Monoid(" ++ typename ++ "): " ++ show i)
  pure (sort monoids)

tryFileDoesNotExist :: IO a -> IO (Maybe a)
tryFileDoesNotExist body =
  catch (Just <$> body) $ \err ->
    if IOE.isDoesNotExistError err
      then pure Nothing
      else throwIO err

readMonoidData :: forall f.
  ( Typeable f, forall a. (Show a) => Show (f a), PTraversable f)
  => Proxy f
  -> FilePath
  -> IO (Maybe [MonoidData (Shape f)])
readMonoidData _ path =
  tryFileDoesNotExist $
    withFile path ReadMode $ \h -> do
      let (as, sig) = makeEnv lengthShape
      dataContent <- lines <$> hGetContents h
      monoids <- case deserializeMonoidDataList as dataContent of
        Left errMsg -> dieWithErrors [errMsg]
        Right (sig', monoids)
          | sig == fmap snd sig' -> pure monoids
          | otherwise           ->
              let errMsg = "Signature mismatch: expected " ++ show sig ++ ", actual " ++ show (snd <$> sig') 
              in dieWithErrors [errMsg]
      for_ monoids $ \mon ->
        validateMonoidData mon
      pure monoids

validateMonoidData :: forall a.
  ( Show a, Enum a, Ord a) => MonoidData a -> IO ()
validateMonoidData monData =
  if null allFails
    then pure ()
    else do hPutStrLn stderr "!Monoid law failure"
            hPutStrLn stderr $ unlines (prettyMonoidData "_" monData)
            dieWithErrors allFails
  where
    monDict = makeMonoidDict monData
    e = monoidUnit monDict
    op = monoidMult monDict

    xs = enum :: [a]
    allFails = unitFails ++ assocFails
    unitFails = do
      x <- xs
      let bad1 = op e x /= x
          msg1 = "leftUnit (" ++ show x ++ ")"
          bad2 = op x e /= x
          msg2 = "rightUnit (" ++ show x ++ ")"
      [ msg1 | bad1 ] ++ [ msg2 | bad2 ]
    assocFails = do
      x <- xs
      y <- xs
      z <- xs
      let bad = (x `op` y) `op` z /= x `op` (y `op` z)
          msg = "assoc " ++ show (x,y,z)
      [ msg | bad ]

-- * Applicative

applicativeGenToFile :: forall f.
  ( Typeable f, forall a. (Show a) => Show (f a), PTraversable f)
  => [ (String, MonoidData (Shape f)) ]
  -> FilePath
  -> Bool
  -> (String -> IO ())
  -> IO [ApplicativeData f]
applicativeGenToFile monoids outFile readIfExist logger = do
  readResult <-
    if readIfExist
      then readApplicativeData outFile
      else pure Nothing
  case readResult of
    Nothing -> do
      applicatives <- applicativeGen monoids logger
      writeFile outFile $ unlines $ serializeApplicativeDataList applicatives
      pure applicatives
    Just applicatives -> pure applicatives

applicativeGen ::
  forall f.
  ( forall a. (Show a) => Show (f a),
    PTraversable f, Typeable f )
  => [ (String, MonoidData (Shape f)) ]
  -> (String -> IO ())
  -> IO [ ApplicativeData f ]
applicativeGen monoids progress = do
  let typename = show (someTypeRep (Proxy :: Proxy f))
      counter = [ 1 :: Int ..]

      applicatives :: [ (String, ApplicativeData f) ]
      applicatives = do
        (monoidName, monData) <- monoids
        applicativeData <- genApplicativeDataFrom monData
        pure (monoidName, applicativeData)
  
  for_ (zip counter applicatives) $ \(i, (monoidName, applicativeData)) -> do
    validateApplicativeData monoidName applicativeData
    progress $ monoidName ++ " => Applicative(" ++ typename ++ "): " ++ show i
  pure (sort $ snd <$> applicatives)

readApplicativeData :: forall f.
  ( Typeable f, forall a. (Show a) => Show (f a), PTraversable f)
  => FilePath
  -> IO (Maybe [ApplicativeData f])
readApplicativeData path =
  tryFileDoesNotExist $
    withFile path ReadMode $ \h -> do
      dataContent <- lines <$> hGetContents h
      applicatives <- case deserializeApplicativeDataList dataContent of
        Left errMsg -> dieWithErrors [errMsg]
        Right applicatives -> pure applicatives
      for_ applicatives $ \apData ->
        validateApplicativeData "_" apData
      pure applicatives

validateApplicativeData :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => String -> ApplicativeData f -> IO ()
validateApplicativeData parentMonName apData
   = if null allFails
       then pure ()
       else do hPutStrLn stderr "!Applicative law failure"
               hPutStrLn stderr $ unlines dump
               dieWithErrors allFails
  where
    apDict@(ApplicativeDict pure' liftA2') = makeApplicativeDict apData
    
    dump :: [String]
    dump = prettyApplicativeDict "_" parentMonName apDict

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

data TwoVars = TwoVars Int Int

instance Show TwoVars where
  show (TwoVars a b) = show a ++ " " ++ show b

prettyApplicativeDict :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => String -> String -> ApplicativeDict f -> [String]
prettyApplicativeDict = docResult
  where
    skolemCache :: [f Int]
    skolemCache = toList skolem
    
    lhsCache :: [String]
    lhsCache = mkLhs <$> strs <*> strs
      where
        showLen x =
          let s = show x
          in (length s, s)
        strs = showLen <$> skolemCache
        maxLen = maximum (0 : fmap fst strs)
        pad (n, s) = s ++ replicate (maxLen - n) ' '
        mkLhs x y  = pad x ++ " <*> " ++ pad y ++ " = "
    
    indent = "  "
    
    docResult apName monoidName dict =
        [ apName <> " = Applicative{" ] ++
        map (indent <>) (
          [ "baseMonoid = " ++ monoidName,
            "pure 0 = " <> show (_applicativePure dict (0 :: Int)) ] ++
          zipWith (<>) lhsCache (show <$> rhs)
        ) ++
        ["}"]
        where
          rhs = _applicativeLiftA2 dict TwoVars <$> skolemCache <*> skolemCache

-- * Monad


monadGenFromApplicativeToFile :: forall f.
  ( Typeable f, forall a. (Show a) => Show (f a), PTraversable f)
  => [ (String, ApplicativeData f) ]
  -> FilePath
  -> MonadGenType
  -> (String -> IO ())
  -> IO [MonadData f]
monadGenFromApplicativeToFile applicatives outFile genType logger = do
  monads <- monadGen applicatives genType logger
  writeFile outFile $ unlines $ serializeMonadDataList monads
  pure monads


monadGenFromApplicativeByType
  :: (forall a. Show a => Show (f a), PTraversable f) => MonadGenType -> ApplicativeDict f -> [ MonadData f ]
monadGenFromApplicativeByType genType = case genType of
  MonadGenV1 -> MonadGen.genFromApplicative
  MonadGenV2 -> MonadGen2.genFromApplicative
  MonadGenV2Cached -> case MonadGen2.prepareGenFromApplicative of
    Nothing -> const []
    Just genPrepared -> genPrepared

monadGen
  :: forall f.
    ( Typeable f, forall a. (Show a) => Show (f a), PTraversable f)
  => [ (String, ApplicativeData f) ]
  -> MonadGenType
  -> (String -> IO ())
  -> IO [MonadData f]
monadGen applicatives genType progress = do
  let typename = show (someTypeRep (Proxy :: Proxy f))
      counter = [ 1 :: Int ..]
      uniq apDict = uniqueByIso @f (ApplicativeData.automorphisms apDict)
      gen = monadGenFromApplicativeByType genType
      
      monads :: [ (String, MonadData f) ]
      monads = do
        (apName, apData) <- applicatives
        let apDict = makeApplicativeDict apData
        monadData <- uniq apDict $ gen apDict
        pure (apName, monadData)
  for_ (zip counter monads) $ \(i, (apName, monadData)) -> do
    progress $ apName ++ " => Monad(" ++ typename ++ "):" ++ show i
    validateMonadDict apName (makeMonadDict monadData)
  pure (snd <$> monads)

validateMonadDict :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => String -> MonadDict f -> IO ()
validateMonadDict apName dict@MonadDict{ _monadPure = pure', _monadJoin = join' }
   = if null allFails
       then pure ()
       else do
        hPutStrLn stderr "!Monad law failure"
        hPutStrLn stderr $ unlines dump
        dieWithErrors allFails
  where
    dump :: [String]
    dump = prettyMonadDict "_" apName dict

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
