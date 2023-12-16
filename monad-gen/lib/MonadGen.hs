{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module MonadGen
  (
    MonadDict(..),
    makeMonadDict,

    MonadData(..),
    genMonads,
    genMonadsModuloIso,
    genMonadsIsoGroups,
  
    genFromApplicative,
    uniqueByIso,
    groupByIso,

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
import qualified Data.LazyVec as Vec
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
import Isomorphism (Iso (..), makePositionIsoFactors)
import Data.Equivalence.Monad

import MonadLaws

-- Monad dictionary

data MonadData f = MonadData (Shape f) (NM.NatMap (f :.: f) f)

deriving instance (WeakEq f, Eq (f (f Ignored)), Eq (f NM.Var)) => Eq (MonadData f)
deriving instance (WeakOrd f, Ord (f (f Ignored)), Ord (f NM.Var)) => Ord (MonadData f)

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
genMonadsModuloIso = 
  do apDict <- makeApplicativeDict <$> genApplicativeData
     uniqueByIso isoGenerators $ genFromApplicative apDict
  where
    isoGenerators = concat makePositionIsoFactors :: [Iso f]

genMonadsIsoGroups :: forall f. (PTraversable f, forall a. (Show a) => Show (f a), forall a. Ord a => Ord (f a)) => [[MonadData f]]
genMonadsIsoGroups = 
  do apDict <- makeApplicativeDict <$> genApplicativeData
     isoGroup <- groupByIso isoGenerators $ genFromApplicative apDict
     pure (Set.toList isoGroup)
  where
    isoGenerators = concat makePositionIsoFactors :: [Iso f]

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
    _f1 :: Vec (f Int),
    _f2 :: Vec (f (f Int)),
    _f3 :: Vec (f (f (f Int)))
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
    _f1 = cache skolem,
    _f2 = cache skolem2,
    _f3 = cache skolem3
  }

_pure :: PTraversable f => Env f -> a -> f a
_pure env = _applicativePure (_baseApplicative env)

runGen :: forall f r. (PTraversable f) => ApplicativeDict f -> Gen f r -> [(r, GenState f)]
runGen apDict mr = runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env = buildInitialEnv apDict

    f3 = _f3 env

    join0 = NM.empty
    blockade = maybe (error "should never happen?") (foldl' unionRel Map.empty) $ traverse newConstraint (Vec.indexed f3)
    newConstraint (k, fa) = foldMap (\blockKey -> singletonRel blockKey k) <$> associativity join0 fa

    state0 :: GenState f
    state0 =
      GenState
        { _join = join0,
          _blockade = blockade
        }

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
        newConstraint k = foldMap (\nextLhsKey -> singletonRel nextLhsKey k) <$> associativity join2 (f3 ! k)
    blockade'' <- case traverse newConstraint (Set.toList blockedAssocs) of
      Nothing -> mzero
      Just newBlockades -> pure $ foldl' unionRel blockade' newBlockades

    modify $ \s ->
      s
        { _join = join2,
          _blockade = blockade''
        }

entryApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Gen f ()
entryApplicative = do
  env <- ask
  let f1 = _f1 env
  for_ f1 $ \fi ->
    for_ f1 $ \fj ->
      let ffij = fmap (\i -> fmap ((,) i) fj) fi
          fk = _applicativeLiftA2 (_baseApplicative env) (,) fi fj
      in entry (Comp1 ffij) fk

guess :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Shape (f :.: f) -> Gen f ()
guess lhsKey = do
  let lhs = keyIndices lhsKey
      lhsVars = toVec lhs
  rhs <- choose (enum1 lhsVars)
  entry lhs rhs

genFromApplicative :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => ApplicativeDict f -> [MonadData f]
genFromApplicative apDict = postproc . snd <$> runGen apDict (entryApplicative >> loop)
  where
    apPure = _applicativePure apDict
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop
    postproc finalState = MonadData (Shape (apPure ())) (_join finalState)

-- * Utilities

keyIndices :: Traversable f => Shape f -> f Int
keyIndices (Shape f1) = _indices f1

-- unsafe access

(!) :: Vec a -> Int -> a
(!) = (Vec.!)

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
