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
    MonadData(..),
    MonadDict(..),
    genMonads,
    genMonadsModuloIso,
    makeMonadDict,

    -- * Debug
    GenState (..),
    Gen,
    runGen,
    genFromMonoid,
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

import MonoidGen (MonoidOn(..), genMonoids)
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
  do monDict <- genMonoids
     genState <- genFromMonoid monDict
     pure $ MonadData (monoidUnit monDict) (_join genState)

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
genMonadsModuloIso = runEquivM id min $ do
    for_ allMonadData $ \mm -> equate mm mm
    for_ allMonadData $ \mm ->
        equateAll (mm : [ applyIso iso mm | iso <- isoGenerators ])
    classes >>= traverse desc
  where
    allMonadData = genMonads :: [MonadData f]
    isoGenerators = concat makePositionIsoFactors :: [Iso f]
    

makeMonadDict :: (PTraversable f) => MonadData f -> MonadDict f
makeMonadDict (MonadData (Shape u) joinMap) = 
    case NM.toTotal joinMap of
      Nothing -> error "well..."
      Just theJoin -> MonadDict (<$ u) (NM.runNT theJoin . Comp1)

-- Generation

type Gen f = ReaderT (Env f) (StateT (GenState f) [])

data Env f = Env
  { _baseMonoid :: MonoidOn f,
    _f1 :: Vec (f Int),
    _f2 :: Vec (f (f Int)),
    _f3 :: Vec (f (f (f Int))),
    _monoidCases :: Map.Map (Shape (f :.: f)) (Shape f)
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
      let join'' = NM.runNT join' . Comp1
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

buildInitialEnv :: forall f. PTraversable f => MonoidOn f -> Env f
buildInitialEnv monDict = Env {
    _baseMonoid = monDict,
    _f1 = f1,
    _f2 = cache skolem2,
    _f3 = cache skolem3,
    _monoidCases = monoidCases
  }
  where
    f1 = cache skolem :: Vec (f Int)
    monoidCases = Map.fromList
      [ (Shape (Comp1 (y <$ x)), monoidMult monDict (Shape x) (Shape y))
        | x <- toList f1,
          y <- toList f1 ]

_pure :: PTraversable f => Env f -> a -> f a
_pure env = case monoidUnit (_baseMonoid env) of
  Shape u -> (<$ u)

runGen :: forall f r. (PTraversable f) => MonoidOn f -> Gen f r -> [(r, GenState f)]
runGen monDict mr = runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env = buildInitialEnv monDict

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
  forall f.
  (forall a. (Show a) => Show (f a), PTraversable f) =>
  (f :.: f) Int ->
  f Int ->
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

entryUU :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Gen f ()
entryUU = do
  env <- ask
  let ui = _indices (_pure env ())
      uuj = fmap (\i -> fmap (\j -> length ui * i + j) ui) ui
      uj = fmap (\i -> length ui * i + i) ui
  entry (Comp1 uuj) uj

entryFUG :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Gen f ()
entryFUG = do
  env <- ask
  let f1 = _f1 env
      ui = _indices (_pure env ())
      n = length ui
      targets = filter (\fj -> Shape fj /= Shape ui) $ Vec.toList f1

      prod gx hy =
        let w = length hy
        in  fmap (\x -> fmap (\y -> w * x + y) hy) gx

  for_ targets $ \fj -> do
    let m = length fj
    let uf = Comp1 (prod ui fj)
    let fu = Comp1 (prod fj ui)
    joinUF <- choose $ traverse (\j -> [ i * m + j | i <- [0 .. n - 1] ]) fj
    entry uf joinUF
    joinFU <- choose $ traverse (\j -> [ j * n + i | i <- [0 .. n - 1] ]) fj
    entry fu joinFU

guess :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Shape (f :.: f) -> Gen f ()
guess lhsKey = do
  let lhs = keyIndices lhsKey
      lhsVars = toVec lhs
  monoidCases <- asks _monoidCases
  rhs <- case Map.lookup lhsKey monoidCases of
    Nothing -> choose (enum1 lhsVars)
    Just rhsKey -> choose $ traverse (const lhsVars) (keyIndices rhsKey)
  entry lhs rhs

genFromMonoid :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => MonoidOn f -> [GenState f]
genFromMonoid mon = snd <$> runGen mon (entryUU >> entryFUG >> loop)
  where
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop

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
