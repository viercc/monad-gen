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

-- Monad dictionary

data MonadData f = MonadData (Shape f) (NM.NatMap (f :.: f) f)

deriving instance (WeakEq f, Eq (f (f Ignored)), Eq (f NM.Var)) => Eq (MonadData f)
deriving instance (WeakOrd f, Ord (f (f Ignored)), Ord (f NM.Var)) => Ord (MonadData f)

signatureOf :: forall f proxy. PTraversable f => proxy f -> [Int]
signatureOf _ = length <$> (shapes :: [f ()])

serializeMonadDataList :: forall f. PTraversable f => [MonadData f] -> [String]
serializeMonadDataList monadData =
  show (signatureOf @f Proxy) : map (show . encodeMonadData) monadData

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
  { _baseApplicative :: ApplicativeDict f,
    _f1 :: V.Vector (f Int),
    _f2 :: V.Vector (f (f Int)),
    _f3 :: V.Vector (f (f (f Int)))
  }

type Join f = NM.NatMap (f :.: f) f

type Blockade f = Rel (Shape (f :.: f)) Int

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
  mapM_ print $ NM.toEntries (_join st)
  putStrLn "----- blockade --"
  putStrLn $ "#blockade = " ++ show (Map.size (_blockade st))
  putStrLn "-----------------"
  case NM.toTotal (_join st) of
    Just join' ->
      let join'' = NM.unwrapNT join' . Comp1
          assoc = flip all skolem3 $ checkAssoc join''
       in unless assoc (fail "!?!?")
    Nothing -> putStrLn "incomplete"

-- (>>=) on Validation
validatedThen :: Validation e a -> (a -> Validation e b) -> Validation e b
validatedThen ea k = case ea of
  Failure e -> Failure e
  Success a -> k a

applyB :: (PTraversable f) => Join f -> f (f a) -> Validation [Shape (f :.: f)] (f a)
applyB m ffa = maybe (Failure [k]) Success $ NM.lookup (Comp1 ffa) m
  where
    k = Shape (Comp1 ffa)

leftAssocB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [Shape (f :.: f)] (f a)
leftAssocB m fffa = applyB m fffa `validatedThen` \ffa -> applyB m ffa

rightAssocB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [Shape (f :.: f)] (f a)
rightAssocB m fffa =
  traverse (applyB m) fffa `validatedThen` \ffa -> applyB m ffa

associativity :: (PTraversable f) => Join f -> f (f (f Int)) -> Maybe [Shape (f :.: f)]
associativity m fffa =
  case (,) <$> leftAssocB m fffa <*> rightAssocB m fffa of
    Success (leftFa, rightFa) -> if leftFa == rightFa then Just [] else Nothing
    Failure blockades -> Just blockades

choose :: (Foldable t) => t a -> Gen f a
choose = lift . lift . toList

buildInitialEnv :: forall f. PTraversable f => ApplicativeDict f -> Env f
buildInitialEnv apDict = Env {
    _baseApplicative = apDict,
    _f1 = skolem,
    _f2 = skolem2,
    _f3 = skolem3
  }

_pure :: Env f -> a -> f a
_pure env = _applicativePure (_baseApplicative env)

_liftA2 :: Env f -> (a -> b -> c) -> f a -> f b -> f c
_liftA2 env = _applicativeLiftA2 (_baseApplicative env)

applicativeToJoin :: (PTraversable f) => Env f -> Maybe (Join f)
applicativeToJoin env = guard isFeasible *> joinMap
  where
    f1 = _f1 env
    isFeasible = length f1 == 1 || not (null (_pure env ()))
    joinMap = NM.fromEntries <$> sequenceA entries
    entries = do
      fi <- V.toList f1
      fj <- V.toList f1
      let lhs = Comp1 $ fmap (\i -> (i,) <$> fj) fi
          rhs = _liftA2 env (,) fi fj
      pure $ NM.makeEntry lhs rhs

testAssociativity :: PTraversable f => Join f -> k -> f (f (f Int)) -> Maybe (Rel (Shape (f :.: f)) k)
testAssociativity join0 k fa = foldMap (\blockKey -> singletonRel blockKey k) <$> associativity join0 fa

runGen :: forall f r. (PTraversable f) => ApplicativeDict f -> Gen f r -> [(r, GenState f)]
runGen apDict mr = do
  join0 <- toList $ applicativeToJoin env
  let t = uncurry (testAssociativity join0)
  blockadeList <- toList $ traverse t (V.indexed f3)
  let blockade = foldl' unionRel Map.empty blockadeList
      state0 =
        GenState
          { _join = join0,
            _blockade = blockade
          }
  runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env = buildInitialEnv apDict

    f3 = _f3 env

entry ::
  forall f b.
  (forall a. (Show a) => Show (f a), PTraversable f) =>
  (Ord b) =>
  (f :.: f) b ->
  f b ->
  Gen f ()
entry lhs rhs =
  do
    join1 <- gets _join
    case NM.lookup lhs join1 of
      Nothing -> return ()
      Just rhs' -> guard (rhs == rhs')
    let join2 = NM.insert (NM.unsafeMakeEntry lhs rhs) join1

    f3 <- asks _f3
    blockade <- gets _blockade

    -- update assocL
    let (blockedAssocs, blockade') = popRel (Shape lhs) blockade
        t k = testAssociativity join2 k (f3 V.! k)
    blockade'' <- case traverse t (Set.toList blockedAssocs) of
      Nothing -> mzero
      Just newBlockades -> pure $ foldl' unionRel blockade' newBlockades

    modify $ \s ->
      s
        { _join = join2,
          _blockade = blockade''
        }

guess :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Shape (f :.: f) -> Gen f ()
guess lhsKey = do
  let lhs = keyIndices lhsKey
  rhs <- choose (enum1 (toList lhs))
  entry lhs rhs

genFromApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicative apDict = postproc . snd <$> runGen apDict loop
  where
    apPure = _applicativePure apDict
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop
    postproc finalState = MonadData (Shape (apPure ())) (_join finalState)

genFromApplicativeModuloIso :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicativeModuloIso apDict = uniqueByIso isoGenerators $ genFromApplicative apDict
  where
    isoGenerators = stabilizingIsomorphisms apDict

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
