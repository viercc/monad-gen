{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}

module MonadGen
  (
    MonadDict(..),
    makeMonadDict,

    MonadData(..),
    genMonads,
    genMonadsModuloIso,
    genMonadsIsoGroups,
  
    genFromApplicative,
    genFromApplicativeViaBinaryJoin,

    moduloIso,
    genFromApplicativeModuloIso,
    genFromApplicativeIsoGroups,

    -- * Read/Write
    serializeMonadDataList,
    deserializeMonadDataList,

    -- * Debug
    GenState (..),
    Gen,
    runGen,
    debugPrint,
    Join,
    Blockade,
  )
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Either.Validation
import Data.Foldable
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import Data.Ord (comparing)
import Data.PTraversable
import Data.PTraversable.Extra
import GHC.Generics ((:.:) (..))
import Data.FunctorShape
import qualified Data.NatMap as NM

-- import MonoidGen (MonoidDict(..), genMonoidsForMonad, makeMonoidDict)
import ApplicativeGen
import Isomorphism (Iso (..))
import Data.Equivalence.Monad

import MonadLaws
import qualified Data.Vector as V
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))
import Text.Read (readMaybe)
import qualified Data.PreNatMap as PNM
import Data.Bifunctor (Bifunctor(..))
import qualified MonadGen.BinaryJoin as BJ
import Data.List (sort)
import Debug.Trace (traceM)

-- Monad dictionary

data MonadData f = MonadData (Shape f) (NM.NatMap (f :.: f) f)

deriving instance (WeakEq f, Eq (f (f Ignored)), Eq (f NM.Var)) => Eq (MonadData f)
deriving instance (WeakOrd f, Ord (f (f Ignored)), Ord (f NM.Var)) => Ord (MonadData f)

signatureOf :: forall f proxy. PTraversable f => proxy f -> [Int]
signatureOf _ = length <$> (shapes :: [f ()])

serializeMonadDataList :: forall f. PTraversable f => [MonadData f] -> [String]
serializeMonadDataList monadData =
  show (signatureOf @f Proxy) : map (show . encodeMonadData) (sort monadData)

deserializeMonadDataList :: forall f. PTraversable f => [String] -> Either String [MonadData f]
deserializeMonadDataList [] = Left "No signature"
deserializeMonadDataList (sigStr : records) =
  do readSig
     traverse parseMonadData (zip [2..] records)
  where
    readSig :: Either String ()
    readSig = case readMaybe sigStr of
      Nothing -> Left "parse error at signature"
      Just sig
        | sig == expectedSig -> Right ()
        | otherwise -> Left "signature mismatch"

    expectedSig :: [Int]
    expectedSig = signatureOf (Proxy :: Proxy f)

    parseMonadData :: (Int, String) -> Either String (MonadData f)
    parseMonadData (lineNo, str) = case readMaybe str of
      Nothing -> Left $ "parse error at line " ++ show lineNo
      Just monadDataRaw -> case decodeMonadData monadDataRaw of
        Nothing -> Left $ "non well-formed MonadData at line " ++ show lineNo
        Just md -> Right md

encodeMonadData :: forall f. PTraversable f => MonadData f -> (Int, [(Int, [Int])])
encodeMonadData (MonadData pureShape joinNM) = (reindex pureShape, encodeEntry <$> joinEntries)
  where
    fIndex :: Set.Set (Shape f)
    fIndex = Set.fromList (Shape <$> shapes)

    reindex sh = fromMaybe (-1) $ Set.lookupIndex sh fIndex

    joinEntries = [ res | Shape ff1 <- NM.keys joinNM, Just res <- [ NM.lookup (_indices ff1) joinNM ] ]
    encodeEntry fn = (reindex (Shape fn), toList fn)

decodeMonadData :: forall f. PTraversable f => (Int, [(Int, [Int])]) -> Maybe (MonadData f)
decodeMonadData (pureIdx, joinData) = MonadData <$> mpureShape <*> mjoinNM
  where
    f1 :: V.Vector (f Int)
    f1 = skolem
    f2 :: V.Vector (f (f Int))
    f2 = skolem2

    mpureShape = Shape <$> (f1 V.!? pureIdx)
    mkEntry (ffn, (rhsIndex, rhsVars)) = 
      do rhsSkolem <- f1 V.!? rhsIndex
         guard (length rhsSkolem == length rhsVars)
         let rhs = fmap (rhsVars !!) rhsSkolem
         NM.makeEntry (Comp1 ffn) rhs
    mjoinNM = do
      joinNM <- NM.fromEntries <$> traverse mkEntry (zip (V.toList f2) joinData)
      guard (NM.size joinNM == V.length f2)
      pure joinNM

data MonadDict f =
  MonadDict {
    _monadPure :: forall a. a -> f a,
    _monadJoin :: forall a. f (f a) -> f a
  }

genMonads :: (PTraversable f, forall a. (Show a) => Show (f a)) => [MonadData f]
genMonads =
  do apDict <- makeApplicativeDict <$> genApplicativeData
     genFromApplicative apDict

applyIso :: PTraversable f => Iso f -> MonadData f -> MonadData f
applyIso (Iso g _) (MonadData u joinNM) = MonadData (mapShape g u) joinNM' 
  where
    joinNM' =
      NM.fromEntries $ do
        (ff1, fx) <- NM.getKeyValue <$> NM.toEntries joinNM
        let ffx = NM.indices ff1
        Just e' <- [ NM.makeEntry (Comp1 . g . fmap g . unComp1 $ ffx) (g fx) ]
        pure e'

genMonadsModuloIso :: forall f. (PTraversable f, forall a. (Show a) => Show (f a), forall a. Ord a => Ord (f a)) => [MonadData f]
genMonadsModuloIso = do
  apDict <- makeApplicativeDict <$> genApplicativeData
  genFromApplicativeModuloIso apDict

genMonadsIsoGroups :: forall f. (PTraversable f, forall a. (Show a) => Show (f a), forall a. Ord a => Ord (f a)) => [[MonadData f]]
genMonadsIsoGroups = 
  do apDict <- makeApplicativeDict <$> genApplicativeData
     isoGroup <- genFromApplicativeIsoGroups apDict
     pure (Set.toList isoGroup)

uniqueByIso :: forall f. (PTraversable f, forall a. (Show a) => Show (f a), forall a. Ord a => Ord (f a))
  => [Iso f] -> [MonadData f] -> [MonadData f]
uniqueByIso isoGenerators allMonadData = runEquivM id min $ do
    for_ allMonadData $ \mm -> equate mm mm
    for_ allMonadData $ \mm ->
      equateAll (mm : [ applyIso iso mm | iso <- isoGenerators ])
    classes >>= traverse desc

groupByIso :: forall f. (PTraversable f, forall a. (Show a) => Show (f a), forall a. Ord a => Ord (f a))
  => [Iso f] -> [MonadData f] -> [Set.Set (MonadData f)]
groupByIso isoGenerators allMonadData = runEquivM Set.singleton Set.union $ do
    for_ allMonadData $ \mm -> equate mm mm
    for_ allMonadData $ \mm ->
      equateAll (mm : [ applyIso iso mm | iso <- isoGenerators ])
    classes >>= traverse desc

makeMonadDict :: (PTraversable f) => MonadData f -> MonadDict f
makeMonadDict (MonadData (Shape u) joinMap) = 
    case NM.toTotal joinMap of
      Nothing -> error "well..."
      Just theJoin -> MonadDict (<$ u) (NM.unwrapNT theJoin . Comp1)

-- Generation

type Gen f = ReaderT (Env f) (StateT (GenState f) [])

data Env f = Env
  { _f1 :: V.Vector (f Int),
    _f2 :: V.Vector (f (f Int)),
    _f3 :: V.Vector (f (f (f Int)))
  }

type Join f = PNM.PreNatMap (f :.: f) f

data BlockReason = UnknownShape | UnknownPos
  deriving (Eq, Ord, Show)
type BlockerKey f = (BlockReason, Shape (f :.: f))
type Blockade f = Rel (BlockerKey f) Int

data GenState f = GenState
  { _pureShape :: Shape f,
    _join :: Join f,
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

applyFull :: (PTraversable f) => Join f -> f (f a) -> Validation [BlockerKey f] (f a)
applyFull m ffa = maybe (Failure [(reason,k)]) Success $ PNM.fullMatch (Comp1 ffa) m
  where
    k = Shape (Comp1 ffa)
    reason = case PNM.lookupShape k m of
      Nothing -> UnknownShape
      Just _  -> UnknownPos

apply :: (PTraversable f, Eq a) => Join f -> f (f a) -> Validation [BlockerKey f] (f a)
apply m ffa = maybe (Failure [(reason,k)]) Success $ PNM.match (Comp1 ffa) m
  where
    k = Shape (Comp1 ffa)
    reason = case PNM.lookupShape k m of
      Nothing -> UnknownShape
      Just _  -> UnknownPos

applyShape :: (PTraversable f) => Join f -> f (f a) -> Validation [BlockerKey f] (Shape f)
applyShape m ffa = maybe (Failure [(UnknownShape,k)]) Success $ PNM.lookupShape k m
  where
    k = Shape (Comp1 ffa)

leftAssocShapeB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [BlockerKey f] (Either (Shape (f :.: f)) (Shape f))
leftAssocShapeB m fffa = secondStep <$> firstStep
  where
    firstStep = apply m (fmap (fmap Shape) fffa)
    secondStep ff = case applyShape m key of
      Failure _ -> Left (Shape (Comp1 key))
      Success f -> Right f
      where key = fmap (\(Shape f) -> void f) ff

rightAssocShapeB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [BlockerKey f] (Either (Shape (f :.: f)) (Shape f))
rightAssocShapeB m fffa = secondStep <$> firstStep
  where
    firstStep = traverse (applyShape m) fffa
    secondStep ff = case applyShape m key of
      Failure _ -> Left (Shape (Comp1 key))
      Success f -> Right f
      where key = fmap (\(Shape f) -> void f) ff

leftAssocB :: (PTraversable f, Eq a) => Join f -> f (f (f a)) -> Validation [BlockerKey f] (Either (BlockReason, (f :.: f) a) (f a))
leftAssocB m fffa = secondStep <$> firstStep
  where
    firstStep = applyFull m fffa
    secondStep ffa = case apply m ffa of
      Failure [] -> error "impossible (the error should be nonempty)"
      Failure ((reason,_) : _) -> Left (reason, Comp1 ffa)
      Success f -> Right f

rightAssocB :: (PTraversable f, Eq a) => Join f -> f (f (f a)) -> Validation [BlockerKey f] (Either (BlockReason, (f :.: f) a) (f a))
rightAssocB m fffa = secondStep <$> firstStep
  where
    firstStep = traverse (applyFull m) fffa
    secondStep ffa = case apply m ffa of
      Failure [] -> error "impossible (the error should be nonempty)"
      Failure ((reason,_) : _) -> Left (reason, Comp1 ffa)
      Success f -> Right f

type Def f a = ((f :.: f) a, f a)
type TestResult f a = ([BlockerKey f], [Def f a])

shapeToDummy :: Functor g => Shape g -> g Int
shapeToDummy (Shape g) = 0 <$ g

associativityShape :: (PTraversable f) => Join f -> f (f (f any)) -> Maybe (TestResult f Int)
associativityShape m fff_ =
  case (,) <$> leftAssocShapeB m fff_ <*> rightAssocShapeB m fff_ of
    Success (leftResult, rightResult) -> case (leftResult, rightResult) of
      (Right f1, Right f2) -> if f1 == f2 then Just ([], []) else Nothing
      (Right f, Left ff) -> Just ([], [(shapeToDummy ff, shapeToDummy f)])
      (Left  ff, Right f) -> Just ([], [(shapeToDummy ff, shapeToDummy f)])
      (Left  ff1, Left ff2) -> Just ([(UnknownShape, ff1), (UnknownShape, ff2)], [])
    Failure blockades -> Just (blockades, [])

associativity :: (PTraversable f) => Join f -> f (f (f Int)) -> Maybe (TestResult f Int)
associativity m fffa =
  case (,) <$> leftAssocB m fffa <*> rightAssocB m fffa of
    Success (leftResult, rightResult) -> case (leftResult, rightResult) of
      (Right fa1, Right fa2) -> if fa1 == fa2 then Just ([], []) else Nothing
      (Right fa, Left (_, ffa)) -> Just ([], [(ffa, fa)])
      (Left  (_,ffa), Right fa) -> Just ([], [(ffa, fa)])
      (Left  (reason1, ffa1), Left (reason2, ffa2)) -> Just ([(reason1, Shape ffa1), (reason2, Shape ffa2)], [])
    Failure blockades -> Just (blockades, [])

choose :: (Foldable t) => t a -> Gen f a
choose = lift . lift . toList

buildInitialEnv :: forall f. PTraversable f => Env f
buildInitialEnv = Env {
    _f1 = skolem,
    _f2 = skolem2,
    _f3 = skolem3
  }

applicativeToJoin :: (PTraversable f) => ApplicativeDict f -> Maybe (NM.NatMap (f :.: f) f)
applicativeToJoin apDict = guard isFeasible *> joinMap
  where
    env = buildInitialEnv
    f1 = _f1 env
    isFeasible = length f1 == 1 || not (null (_applicativePure apDict ()))
    joinMap = NM.fromEntries <$> sequenceA entries
    entries = do
      fi <- V.toList f1
      fj <- V.toList f1
      let lhs = Comp1 $ fmap (\i -> (i,) <$> fj) fi
          rhs = _applicativeLiftA2 apDict (,) fi fj
      pure $ NM.makeEntry lhs rhs

testAssociativityShape :: PTraversable f => Join f -> k -> f (f (f Int)) -> Maybe (Rel (BlockerKey f) k, [Def f Int])
testAssociativityShape join0 k fa = first toRel <$> associativityShape join0 fa
  where
    toRel = foldMap (\blockKey -> singletonRel blockKey k)

testAssociativity :: PTraversable f => Join f -> k -> f (f (f Int)) -> Maybe (Rel (BlockerKey f) k, [Def f Int])
testAssociativity join0 k fa = first toRel <$> associativity join0 fa
  where
    toRel = foldMap (\blockKey -> singletonRel blockKey k)

firstScan :: (PTraversable f) => Env f -> Join f -> Maybe ([Def f Int], Blockade f)
firstScan env join0 = do
  initialResults1 <- traverse t1 (V.indexed f3)
  initialResults2 <- traverse t2 (V.indexed f3)
  let initialResults = V.toList initialResults1 ++ V.toList initialResults2
      blockade = foldl' unionRel Map.empty (fst <$> initialResults)
      defs = initialResults >>= snd
  Just (defs, blockade)
  where
    f3 = _f3 env
    t1 = uncurry (testAssociativityShape join0)
    t2 = uncurry (testAssociativity join0)

runGen :: forall f r. (PTraversable f) => Shape f -> Join f -> Gen f r -> [(r, GenState f)]
runGen pureShape join0 mr = do
  (defs, blockade) <- toList $ firstScan env join0
  let state0 =
        GenState
          { _pureShape = pureShape,
            _join = join0,
            _blockade = blockade
          }
  runStateT (runReaderT (entryLoop defs >> mr) env) state0
  where
    env :: Env f
    env = buildInitialEnv

repair :: PTraversable f => BlockerKey f -> Gen f [Def f Int]
repair (reason, key) = do
  join1 <- gets _join
  blockade <- gets _blockade
  f3 <- asks _f3

  let (blockedEqs, blockade') = popRel (reason, key) blockade
      toResult k (newBlockers, newDefs) = (foldMap (\blocker -> singletonRel blocker k) newBlockers, newDefs)
      test k = toResult k <$> associativity join1 (f3 V.! k)
  (blockade'', newDefs) <- case traverse test (Set.toList blockedEqs) of
    Nothing -> mzero
    Just results ->
      let blockade'' = foldl' unionRel blockade' (fst <$> results)
          newDefs = concatMap snd results
      in pure (blockade'', newDefs)
  
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
    join2 <- choose $ PNM.refine lhs rhs join1

    modify $ \s -> s { _join = join2 }
    
    -- update assoc
    newShapeDefs <- repair (UnknownShape, Shape lhs)
    newDefs <- repair (UnknownPos, Shape lhs)
    
    pure (newShapeDefs ++ newDefs)

entryLoop :: 
  forall f. (PTraversable f) =>
  [Def f Int] -> Gen f ()
entryLoop [] = pure ()
entryLoop (def : defs) = do
  newDefs <- entry def
  entryLoop (newDefs ++ defs)

guess :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => BlockerKey f -> Gen f ()
guess (UnknownShape, lhsKey) = do
  -- Make a shape-only guess
  let lhs = shapeToDummy lhsKey
  rhs <- choose (enum1 [0])
  entryLoop [(lhs, rhs)]
guess (UnknownPos, lhsKey) = do
  -- Make a shape-only guess
  join1 <- gets _join
  let lhs = keyIndices lhsKey
  rhs <- case PNM.lookup (Set.singleton <$> lhs) join1 of
    -- expect this not to happen, as (UnknownPos, key) should not be generated
    -- if (UnknonShape, key) is already resolved
    Nothing -> error "impossible?"
    Just rhsSet -> choose (traverse Set.toList rhsSet)
  entryLoop [(lhs, rhs)]

genFromApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicative apDict = do
  apJoin <- toList $ applicativeToJoin apDict
  postproc . snd <$> runGen pureShape (PNM.fromNatMap apJoin) loop
  where
    pureShape = Shape (_applicativePure apDict ())
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop
    postproc finalState = MonadData (_pureShape finalState) (PNM.toNatMap (_join finalState))

genFromApplicativeViaBinaryJoin :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicativeViaBinaryJoin apDict = do
  let allBinaryJoins = BJ.genFromApplicative apDict
  traceM $ "#binaryJoin = " ++ show (length allBinaryJoins)
  binaryJoin <- allBinaryJoins
  postproc . snd <$> runGen pureShape (BJ.binaryJoinToJoin binaryJoin) loop
  where
    pureShape = Shape (_applicativePure apDict ())
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop
    postproc finalState = MonadData (_pureShape finalState) (PNM.toNatMap (_join finalState))

moduloIso :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f] -> [MonadData f]
moduloIso apDict = uniqueByIso isoGenerators
  where
    isoGenerators = stabilizingIsomorphisms apDict

genFromApplicativeModuloIso :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicativeModuloIso apDict = moduloIso apDict $ genFromApplicative apDict

genFromApplicativeIsoGroups :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [Set.Set (MonadData f)]
genFromApplicativeIsoGroups apDict = groupByIso isoGenerators $ genFromApplicative apDict
  where
    isoGenerators = stabilizingIsomorphisms apDict

-- * Utilities

keyIndices :: Traversable f => Shape f -> f Int
keyIndices (Shape f1) = _indices f1

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
    (kTop, _) = maximumBy (comparing (Set.size . snd)) $ Map.toList m
