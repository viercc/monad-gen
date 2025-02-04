{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import C.Act qualified as Act
import C
import Control.Arrow ((&&&))
import Control.Comonad (Comonad (..))
import Data.Coerce (coerce)
import Data.Finitary (Finitary, inhabitants)
import Data.Finitary.Extra (prettyPrintFn, prettyPrintFn2, sequenceFn)
import Data.Foldable (for_)
import Data.Group
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.ZMod (Bit (..), ZMod)
import C.St
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO
import Text.Read (readMaybe)

newtype A = A Bit
  deriving (Show, Read, Eq, Finitary, Semigroup, Monoid, Group) via Bit

newtype B = B Bit
  deriving (Show, Read, Eq, Finitary, Semigroup, Monoid, Group) via Bit

main :: IO ()
main = getArgs >>= main'
  where
    main' args = case args of
      _ | "--help" `elem` args -> printUsage
      [] -> generateToFile defaultCacheFileName >>= diagnosis
      ["--cached"] -> readCache defaultCacheFileName >>= diagnosis
      ("--cached" : filename : _) -> readCache filename >>= diagnosis
      _ -> printUsage

printUsage :: IO ()
printUsage =
  putStrLn $
    unlines
      ["comonad-dist-gen [--help | --cached [FILENAME]]"]

defaultCacheFileName :: FilePath
defaultCacheFileName = "comonad-dist-gen.cache"

generateToFile :: FilePath -> IO [LensCode]
generateToFile cacheFileName = do
  putStrLn "# Generating lawful DistLens..."
  let generatedData = encodeLens <$> generateAll ()
  mapM_ print generatedData
  putStrLn $ "Write the generated data to cache file:" ++ show cacheFileName
  writeFile cacheFileName (show generatedData)
  pure generatedData

{-
Even for this smallest case, simply enumerating every lenses
is not possible.

  ghci> :kind! Cardinality (DistLens A B)
  Cardinality (DistLens A B) :: GHC.Num.Natural.Natural
  = 309485009821345068724781056

Few considerations of distributive law laws @law1@ and @law2@
yields few conditions on @Dist A B@, which reduces the number down to
"only" 2^24 candidates.

This makeshift optimization isn't effective at all for anything
larger. While @generateCandidateLenses@ function is written
in a way independent of chocies of type @A, B@, it it provided
monomorphic to prevent misusing it on "too hard" case,
in other words any other nontrivial condition.

-}

generateCandidateLenses :: () -> [DistLens A B]
generateCandidateLenses _ = map Lens $ sequenceFn $ \sst -> do
  let (C s0 f) = sst
  let t0 = f s0
  f' <- sequenceFn $ \t' -> if t' == t0 then [s0] else inhabitants
  putPart <- sequenceFn $ \case
    (t, s)
      | t == t0 -> [(s, f s)]
      | s == f' t -> [(s0, t)]
      | otherwise -> inhabitants
  pure (C t0 f', putPart)

generateAll :: () -> [DistLens A B]
generateAll u = filter checkAllLaws (generateCandidateLenses u)

readCache :: FilePath -> IO [LensCode]
readCache cacheFileName = do
  putStrLn $ "# Reading cached file:" ++ show cacheFileName
  cachedDataStr <- readFile' cacheFileName
  case readMaybe cachedDataStr of
    Nothing -> hPutStrLn stderr "Cache file couldn't be parsed" >> exitFailure
    Just generatedData -> pure generatedData

diagnosis :: [LensCode] -> IO ()
diagnosis generatedData = do
  putStrLn "# Is the data all valid?"
  generatedLenses <- case traverse decodeLens generatedData of
    Nothing -> hPutStrLn stderr "Bad data!" >> exitFailure
    Just lenses -> pure lenses
  putStrLn "# Pretty-print the generated lenses:"
  prettyPrintDistLenses generatedLenses
  prettyPrintDistLensesAct generatedLenses
  putStrLn "# Are the generated lenses isomorphic each other?"
  printIsoTable generatedData
  putStrLn "# Check that handcrafted distributive laws are valid"
  printHandcraftedDistLens

prettyPrintDistLenses :: [DistLens A B] -> IO ()
prettyPrintDistLenses generatedData = for_ (zip [0 :: Int ..] generatedData) $ \(i, lens) -> do
  putStrLn $ "## Dist" ++ show i
  for_ (prettyPrintDistLens lens) $ \pprLine ->
    putStrLn $ "  " ++ pprLine

prettyPrintDistLensesAct :: [DistLens A B] -> IO ()
prettyPrintDistLensesAct generatedData = for_ (zip [0 :: Int ..] generatedData) $ \(i, lens) -> do
  putStrLn $ "## Dist" ++ show i ++ " (as group action comonad)"
  for_ (prettyPrintDistLens (distLensAsActDistLens lens)) $ \pprLine ->
    putStrLn $ "  " ++ pprLine

printIsoTable :: [LensCode] -> IO ()
printIsoTable lenses = mapM_ (putStrLn . List.intercalate "|" . map toSymb) (isoTable lenses)
  where
    toSymb b = if b then "==" else "  "

printHandcraftedDistLens :: IO ()
printHandcraftedDistLens = do
  putStrLn "### Dist0"
  putStrLn $ "Code:     " ++ show (encodeLens distLens0)
  putStrLn $ "Validity: " ++ show (checkAllLaws distLens0)
  putStrLn $ "Is dist0 correct? " ++ show (distToLens dist0 == distLens0)
  putStrLn $ "Is distByGroup correct? " ++ show (distToLens distByGroup == distLens0)

  putStrLn "### distByGroup"
  let distByGroup_2_3 = distToLens (distByGroup @(St Bool) @(ZMod 3))
  putStrLn $ "dist := distByGroup @(Store Bool) @(ZMod 3)"
  putStrLn $ "Code: " ++ show (encodeLens distByGroup_2_3)
  putStrLn $ "Validity: " ++ show (checkAllLaws distByGroup_2_3)

  putStrLn "### Dist1"
  putStrLn $ "Code:     " ++ show (encodeLens distLens1)
  putStrLn $ "Validity: " ++ show (checkAllLaws distLens1)

prettyPrintDistLens :: DistLens A B -> [String]
prettyPrintDistLens l =
  pprLetIn (prettyPrintFn "q" q ++ prettyPrintFn2 "d0" d0 ++ prettyPrintFn2 "d1" d1) ["Lens $ \\c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))"]
  where
    q :: (A, B, B) -> (B, A, A)
    q = view . coerce . fst . unLens l . coerce . review

    d0 :: (A, B, B) -> (B, A) -> A
    d0 = fmap fst . snd . unLens l . coerce . review

    d1 :: (A, B, B) -> (B, A) -> B
    d1 = fmap snd . snd . unLens l . coerce . review

    indent = ("    " ++)
    pprLetIn _ [] = error "empty let-body?"
    pprLetIn [] _ = error "empty let-defs?"
    pprLetIn (firstDefLine : letLines) (firstBodyLine : inLines) =
      ["let " ++ firstDefLine]
        ++ map indent letLines
        ++ ["in  " ++ firstBodyLine]
        ++ map indent inLines

    view :: C a Bit b -> (a, b, b)
    view (C a f) = (a, f 0, f 1)

    review :: (a, b, b) -> C a Bit b
    review (a, b0, b1) = C a $ \bit -> if bit == 0 then b0 else b1

-- | Comonad automorphism
--
-- Every comonad automorphism of a store comonad @C S S@
-- come from an automorphism @(σ :: S -> S)@, as
-- @mapPos σ . mapPort σ⁻¹@
comonadAuto :: forall a x. (a -> a) -> (a -> a) -> St a x -> St a x
comonadAuto f fInv = St . mapC f fInv . unSt

translate :: DistLens A B -> [DistLens A B]
translate l =
  [ distToLens (actB gB . fmap (actA gA) . dist . fmap (actB (inv gB)) . actA (inv gA))
  | gA <- [False, True],
    gB <- [False, True]
  ]
  where
    dist :: Dist (St A) (St B)
    dist = distFromLens l

    inv = id

    actA :: forall x. Bool -> St A x -> St A x
    actA b = if b then coerce (comonadAuto @Bool @x not not) else id

    actB :: forall x. Bool -> St B x -> St B x
    actB = coerce (actA @x)

isoTable :: [LensCode] -> [[Bool]]
isoTable generatedData = [[(i, j) `Set.member` isoRelation | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]
  where
    n = length generatedData
    revMap = Map.fromList (zip generatedData [0 ..])
    isoList = do
      (encLens, i) <- Map.toList revMap
      let lens = decodeLens' encLens
      otherLens <- translate lens
      let encOtherLens = encodeLens otherLens
      case Map.lookup encOtherLens revMap of
        Nothing -> error "what!?"
        Just j -> pure (i, j)
    isoRelation = Set.fromList isoList

-- Simplify and Dist #0 as A = B = Bit
distLens0 :: DistLens Bit Bit
distLens0 = Lens $ \c -> (q c, d0 c &&& d1 c)
  where
    q (C a f) = C (f a) (const a)
    d0 _ (_, a) = a
    d1 (C a0 f) (b, a) = b - f a0 + f a

-- dist0 = distFromLens distLens0
dist0 :: Dist (St Bit) (St Bit)
dist0 (St (C a0 k)) = St $ C (f a0) $ \b -> St $ C a0 $ \a -> h a (b - f a0 + f a)
  where
    f = pos . unSt . k
    h a b = peek (unSt (k a)) b

distLens1 :: DistLens Bit Bit
distLens1 = Lens $ \c -> (q c, d0 (view c) &&& d1 (view c))
  where
    view (C a0 f) = (a0, f 0, f 1)

    q (C 0 f) = C (f 0) $ \b -> if f b > f (1 + b) then 1 else 0
    q (C _ f) = C (f 1) $ \b -> if f b >= f (1 + b) then 1 else 0

    d0_5 (_, a) = a
    d0_6 (b, a) = b + a
    d0_9 (b, a) = 1 + b + a

    d0 (0, 0, 0) = d0_5
    d0 (0, 0, 1) = d0_6
    d0 (0, 1, 0) = d0_9
    d0 (0, 1, 1) = d0_5
    d0 (1, 0, 0) = d0_5
    d0 (1, 0, 1) = d0_9
    d0 (1, 1, 0) = d0_6
    d0 (1, 1, 1) = d0_5
    d0 _ = undefined

    d1_3 (b, _) = b
    d1_5 (_, a) = a
    d1_10 (_, a) = 1 + a

    d1 (0, 0, 0) = d1_3
    d1 (0, 0, 1) = d1_5
    d1 (0, 1, 0) = d1_10
    d1 (0, 1, 1) = d1_3
    d1 (1, 0, 0) = d1_3
    d1 (1, 0, 1) = d1_5
    d1 (1, 1, 0) = d1_10
    d1 (1, 1, 1) = d1_3
    d1 _ = undefined

-- | Distributive law by group
distByGroup :: forall w g. (Comonad w, Group g) => forall x. w (St g x) -> St g (w x)
distByGroup = Act.toSt . Act.distDefault . fmap Act.fromSt

---- display as Act

distToActDist :: (Group s, Group t) => Dist (St s) (St t) -> Dist (Act.Act s) (Act.Act t)
distToActDist stDist = Act.fromSt . fmap Act.fromSt . stDist . Act.toSt . fmap Act.toSt

distLensAsActDistLens :: (Group s, Group t) => DistLens s t -> Act.DistLens s t
distLensAsActDistLens lens = Act.distToLens (distToActDist (distFromLens lens))