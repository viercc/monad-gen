{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{- HLINT ignore "Use camelCase" -}

module MonadGen
  (
    module MonadData,

    genFromMonoid,

    genFromApplicative,
    genFromApplicativeViaBinaryJoin,

    -- * Debug
    GenState (..),
    Gen,
    runGen,
    debugPrint,
    Join,
    Blockade,
  )
where

import qualified Data.Foldable as F
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Data.Map.Lazy as Map
import qualified Data.NatMap as NM
import qualified Data.PreNatMap as PNM
import qualified Data.Bitmap as Bitmap
import qualified Data.List.NonEmpty as NE
import qualified Data.IntMap.Strict as IntMap

import Data.Bifunctor (Bifunctor(..))
import Data.Either.Validation ( Validation(..), eitherToValidation )
import Data.Ord (comparing)
import GHC.Generics ((:.:) (..))

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

import Data.PTraversable
import Data.PTraversable.Extra
import Data.FunctorShape

import MonoidGen (MonoidDict(..))
import ApplicativeData ( ApplicativeDict(..) )

import Debug.Trace (traceM)

import MonadData
import MonadLaws
import qualified MonadGen.BinaryJoin as BJ
import Data.Traversable.Extra (indices, zipMatchWith)

-- * Entry points

genFromMonoid :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => MonoidDict (Shape f) -> [MonadData f]
genFromMonoid monDict = do
  monDefs <- F.toList $ monoidToJoin monDict
  postproc . snd <$> runGen buildInitialEnv (initialize monDefs >> loop)
  where
    pureShape = monoidUnit monDict
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop
    postproc finalState = MonadData pureShape (PNM.toNatMap (_join finalState))

genFromApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicative apDict = do
  apJoin <- F.toList $ applicativeToJoin apDict
  postproc . snd <$> runGen buildInitialEnv (initialize (PNM.fromNatMap apJoin) >> loop)
  where
    pureShape = Shape (_applicativePure apDict ())
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop
    postproc finalState = MonadData pureShape (PNM.toNatMap (_join finalState))

genFromApplicativeViaBinaryJoin :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicativeViaBinaryJoin apDict = do
  let allBinaryJoins = BJ.genFromApplicative apDict
  traceM $ "#binaryJoin = " ++ show (length allBinaryJoins)
  binaryJoin <- allBinaryJoins
  postproc . snd <$> runGen buildInitialEnv (initialize (BJ.binaryJoinToJoin binaryJoin) >> loop)
  where
    pureShape = Shape (_applicativePure apDict ())
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop
    postproc finalState = MonadData pureShape (PNM.toNatMap (_join finalState))

-- Generation internals

type Gen f = ReaderT (Env f) (StateT (GenState f) [])

data Env f = Env
  { _f1 :: V.Vector (f Int),
--    _shapeEqs :: V.Vector (f (f (f Int))),
    _fullEqs :: V.Vector (f (f (f Int)))
  }

type Join f = PNM.PreNatMap (f :.: f) f

type BlockerKey f = (Shape (f :.: f))
type Blockade f = Rel (BlockerKey f) Int

data GenState f = GenState
  { _join :: Join f,
    _blockade :: Blockade f
  }

debugPrint ::
  (PTraversable f, forall a. (Show a) => Show (f a)) =>
  GenState f ->
  IO ()
debugPrint st = do
  putStrLn "----- join ------"
  mapM_ print $ PNM.toEntries (_join st)
  putStrLn "----- blockade --"
  putStrLn $ "#blockade = " ++ show (Map.size (_blockade st))
  putStrLn "-----------------"
  case NM.toTotal (PNM.toNatMap (_join st)) of
    Just join' ->
      let join'' = NM.unwrapNT join' . Comp1
          assoc = flip all skolem3 $ checkAssoc join''
       in unless assoc (fail "!?!?")
    Nothing -> putStrLn "incomplete"

type BlockableEval f = Validation (NE.NonEmpty (BlockerKey f))

apply :: (PTraversable f, Eq a) => Join f -> f (f a) -> Either (f (f a)) (f a)
apply m ffa = case PNM.match (Comp1 ffa) m of
    Nothing -> Left ffa
    Just fa -> Right fa

applyB :: (PTraversable f, Eq a) => Join f -> f (f a) -> BlockableEval f (f a)
applyB m = eitherToValidation . first (NE.singleton . Shape . Comp1) . apply m

leftAssocB :: (PTraversable f, Eq a) => Join f -> f (f (f a)) -> BlockableEval f (Either (f (f a)) (f a))
leftAssocB m fffa = apply m <$> firstStep
  where
    firstStep = applyB m fffa

rightAssocB :: (PTraversable f, Eq a) => Join f -> f (f (f a)) -> BlockableEval f (Either (f (f a)) (f a))
rightAssocB m fffa = apply m <$> firstStep
  where
    firstStep = traverse (applyB m) fffa

type Def f a = ((f :.: f) a, f a)
type TestResult f a = ([BlockerKey f], [Def f a])

associativity :: (PTraversable f) => Join f -> f (f (f Int)) -> Maybe (TestResult f Int)
associativity m fffa =
  case (,) <$> leftAssocB m fffa <*> rightAssocB m fffa of
    Success bothSides -> case bothSides of
      (Right fa1, Right fa2) -> if fa1 == fa2 then Just ([], []) else Nothing
      (Right fa, Left ffa) -> Just ([], [(Comp1 ffa, fa)])
      (Left  ffa, Right fa) -> Just ([], [(Comp1 ffa, fa)])
      (Left  ffa1, Left ffa2) -> do
        defs <- constraintsFromEq m ffa1 ffa2
        pure ([Shape (Comp1 ffa1), Shape (Comp1 ffa2)], defs)
    Failure blockades -> Just (NE.toList blockades, [])

constraintsFromEq :: (PTraversable f) => Join f -> f (f Int) -> f (f Int) -> Maybe [Def f Int]
constraintsFromEq m ffa ffb = case (lup (Comp1 ffa), lup (Comp1 ffb)) of
  (Nothing, Nothing) -> pure []
  (Just fA, Nothing) -> oneSidedCase fA ffb
  (Nothing, Just fB) -> oneSidedCase fB ffa
  (Just fA, Just fB) -> do
    fC <- zipMatchWith (\aa bb -> NE.nonEmpty (Bitmap.toList (Bitmap.intersection aa bb))) fA fB
    let sigma = substFromPartitions (F.toList fC)
        fc = NE.head <$> fC
        ffa' = applySubst sigma <$> Comp1 ffa
        ffb' = applySubst sigma <$> Comp1 ffb
    pure [(ffa',fc), (ffb',fc)]

  where
    lup x = PNM.lookupWith Bitmap.singleton x m

    oneSidedCase fX ffy = do
      fX' <- traverse (NE.nonEmpty . Bitmap.toList) fX
      let sigma = substFromPartitions (F.toList fX')
          fx = NE.head <$> fX'
          ffy' = applySubst sigma <$> Comp1 ffy
      pure [(ffy', fx)]


choose :: (Foldable t) => t a -> Gen f a
choose = lift . lift . F.toList

buildInitialEnv :: forall f. PTraversable f => Env f
buildInitialEnv = Env {
    _f1 = skolem,
    _fullEqs = skolem3
  }

applicativeToJoin :: (PTraversable f) => ApplicativeDict f -> Maybe (NM.NatMap (f :.: f) f)
applicativeToJoin apDict = guard isFeasible *> joinMap
  where
    env = buildInitialEnv
    f1 = _f1 env
    isFeasible = length f1 == 1 || not (null (_applicativePure apDict ()))
    joinMap = do
      apDefsMap <- mapFromListUnique apDefs
      entries <- traverse (uncurry NM.makeEntry) (Map.toList apDefsMap)
      pure $ NM.fromEntries entries
    apDefs = do
      fi <- V.toList f1
      fj <- V.toList f1
      let lhs = Comp1 $ fmap (\i -> (i,) <$> fj) fi
          rhs = _applicativeLiftA2 apDict (,) fi fj
      [(lhs, rhs)]

monoidToJoin :: (PTraversable f) => MonoidDict (Shape f) -> Maybe (PNM.PreNatMap (f :.: f) f)
monoidToJoin monDict = PNM.fromEntries (monDefs ++ unitLaws)
  where
    fs = V.toList skolem
    monDefs = monDef <$> fs <*> fs
    monDef f1 f2 =
      case monoidMult monDict (Shape f1) (Shape f2) of
        Shape f' -> (Comp1 ((0 <$ f2) <$ f1), 0 <$ f')
    
    _pure a = case monoidUnit monDict of
      Shape u -> a <$ u
      
    unitLaws = [leftUnit, rightUnit] <*> fs
    leftUnit f = (Comp1 (_pure f), f)
    rightUnit f = (Comp1 (_pure <$> f), f)

-- Map.fromList but the values for the repeated keys must be unique
mapFromListUnique :: (Ord k, Eq v) => [(k,v)] -> Maybe (Map.Map k v)
mapFromListUnique = F.foldlM step Map.empty
  where
    step m (k,v) = Map.alterF (checkedInsert v) k m
    checkedInsert newV old = case old of
      Nothing -> Just (Just newV)
      Just oldV -> old <$ guard (newV == oldV)

testAssociativity :: PTraversable f => Join f -> k -> f (f (f Int)) -> Maybe (Rel (BlockerKey f) k, [Def f Int])
testAssociativity join0 k fa = first toRel <$> associativity join0 fa
  where
    toRel = foldMap (\blockKey -> singletonRel blockKey k)

firstScan :: (PTraversable f) => Env f -> Join f -> Maybe ([Def f Int], Blockade f)
firstScan env join0 = do
  initialResults <- V.toList <$> traverse t (V.indexed eqs)
  let blockade = foldl' unionRel Map.empty (fst <$> initialResults)
      defs = initialResults >>= snd
  Just (defs, blockade)
  where
    eqs = _fullEqs env
    t = uncurry (testAssociativity join0)

initialize :: (PTraversable f) => Join f -> Gen f ()
initialize join0 = do
  env <- ask
  (defs, blockade) <- choose $ firstScan env join0
  put GenState { _join = join0, _blockade = blockade }
  entryLoop defs

runGen :: forall f r. (PTraversable f) => Env f -> Gen f r -> [(r, GenState f)]
runGen env mr = runStateT (runReaderT mr env) emptyState
  where
    emptyState = GenState PNM.empty Map.empty

repair :: PTraversable f => Shape (f :.: f) -> Gen f [Def f Int]
repair key = do
  join1 <- gets _join
  blockade <- gets _blockade
  eqs1 <- asks _fullEqs

  let (blockedEqs, blockade') = popRel key blockade
      toResult k (newBlockers, newDefs) = (foldMap (\blocker -> singletonRel blocker k) newBlockers, newDefs)
      test k = toResult k <$> associativity join1 (eqs1 V.! k)
  testResults <- choose $ traverse test (Set.toList blockedEqs)
  let blockade'' = foldl' unionRel blockade' (fst <$> testResults)
      newDefs = concatMap snd testResults
  
  modify $ \s -> s{ _blockade = blockade'' }
  pure newDefs

entry ::
  forall f b.
  Ord b => (PTraversable f) =>
  Def f b -> Gen f [Def f Int]
entry (lhs, rhs) =
  do
    join1 <- gets _join
    -- fail on Nothing case
    (changed, join2) <- choose $ PNM.refine' lhs rhs join1
    
    if changed
      then do
        modify $ \s -> s { _join = join2 }
        repair (Shape lhs)
      else pure []

entryLoop :: 
  forall f. (PTraversable f) =>
  [Def f Int] -> Gen f ()
entryLoop [] = pure ()
entryLoop (def : defs) = do
  newDefs <- entry def
  entryLoop (newDefs ++ defs)

guess :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => BlockerKey f -> Gen f ()
guess lhsKey = do
  join1 <- gets _join
  f1 <- asks _f1
  let lhs = keyIndices lhsKey
  case PNM.lookup (Bitmap.singleton <$> lhs) join1 of
    Nothing -> do
      -- Make a shape-only guess
      rhs <- choose f1
      entryLoop [(0 <$ lhs, 0 <$ rhs)]
    Just rhsSet -> do
      -- Make a position guess
      rhs <- choose (traverse Bitmap.toList rhsSet)
      entryLoop [(lhs, rhs)]

-- * Utilities

keyIndices :: Traversable f => Shape f -> f Int
keyIndices (Shape f1) = indices f1

-- Relation data structure

type Rel a b = Map.Map a (Set.Set b)

singletonRel :: a -> b -> Rel a b
singletonRel a b = Map.singleton a (Set.singleton b)

unionRel :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
unionRel = Map.unionWith Set.union

popRel :: (Ord a, Ord b) => a -> Rel a b -> (Set.Set b, Rel a b)
popRel k m = case Map.lookup k m of
  Nothing -> (Set.empty, m)
  Just s -> (s, Map.delete k m)

mostRelated :: (Ord a) => Rel a b -> Maybe a
mostRelated m
  | Map.null m = Nothing
  | otherwise = Just kTop
  where
    (kTop, _) = F.maximumBy (comparing (Set.size . snd)) $ Map.toList m

-- Substitions

type Subst = IntMap.IntMap Int

applySubst :: Subst -> Int -> Int
applySubst sigma i = IntMap.findWithDefault i i sigma

-- | Makes a Subst mapping each Int to the least element of
--   the class it belongs.
--
-- Assumption:
-- - NonEmpty lists represent a equivalence class.
--   Elements must be sorted in ascending order.
-- - NonEmpty lists may have duplicates, but should not
--   intersect with distinct lists.
--   in other words, either equal or disjoint each other.
substFromPartitions :: [NE.NonEmpty Int] -> Subst
substFromPartitions = IntMap.fromList . concatMap toEntry
  where
    toEntry (x NE.:| xs) = [ (y,x) | y <- xs ]