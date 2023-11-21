{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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
import qualified Data.Map as Map
import Data.Ord (comparing)
import Data.PTraversable
import Data.PTraversable.Extra
import GHC.Generics ((:.:) (..))
import qualified NatMap as NM
import Set1 (Key (), key, unkey)
import qualified Set1 as S1

import MonoidGen (MonoidOn(..), genMonoids)
import Isomorphism (Iso (..), makePositionIsoFactors)
import Data.Equivalence.Monad

import MonadLaws

-- Monad dictionary

data MonadData f = MonadData (f ()) (NM.NatMap (f :.: f) f)

deriving instance (Eq (f ()), Eq (f NM.Var)) => Eq (MonadData f)
deriving instance (Ord (f ()), Ord (f NM.Var)) => Ord (MonadData f)

data MonadDict f =
  MonadDict {
    _monadPure :: forall a. a -> f a,
    _monadJoin :: forall a. f (f a) -> f a
  }

genMonads :: (PTraversable f, forall a. (Show a) => Show (f a)) => [MonadData f]
genMonads =
  do monDict <- genMonoids
     genState <- genFromMonoid monDict
     pure $ MonadData (unkey (monoidUnit monDict)) (_join genState)

applyIso :: PTraversable f => Iso f -> MonadData f -> MonadData f
applyIso (Iso g g') (MonadData u joinNM) = MonadData (g u) joinNM' 
  where
    joinNM' = NM.toTotal joinNM (error "non-total join?") $ \join' ->
      NM.fromNat (g . join' . Comp1 . g' . fmap g' . unComp1)

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
makeMonadDict (MonadData u joinMap) = 
    NM.toTotal joinMap (error "well...") $ \theJoin -> MonadDict (<$ u) (theJoin . Comp1)

-- Generation

type Gen f = ReaderT (Env f) (StateT (GenState f) [])

data Env f = Env
  { _baseMonoid :: MonoidOn f,
    _f1 :: Vec (f Int),
    _f2 :: Vec (f (f Int)),
    _f3 :: Vec (f (f (f Int))),
    _monoidCases :: Map.Map (JoinKey f) (Key f)
  }

type Join f = NM.NatMap (f :.: f) f

type JoinKey f = Key (f :.: f)

type Blockade f = Rel (JoinKey f) (f :.: f :.: f)

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
  putStrLn (NM.debug (_join st))
  putStrLn "----- blockade --"
  putStrLn $ "#blockade = " ++ show (Map.size (_blockade st))
  putStrLn "-----------------"
  NM.toTotal
    (_join st)
    (putStrLn "Not completed yet")
    $ \join' ->
      let join'' = join' . Comp1
          assoc = flip all skolem3 $ checkAssoc join''
       in unless assoc (fail "!?!?")

-- (>>=) on Validation
validatedThen :: Validation e a -> (a -> Validation e b) -> Validation e b
validatedThen ea k = case ea of
  Failure e -> Failure e
  Success a -> k a

applyB :: (PTraversable f) => Join f -> f (f a) -> Validation [JoinKey f] (f a)
applyB m ffa = maybe (Failure [k]) Success $ NM.lookup (Comp1 ffa) m
  where
    k = key (Comp1 ffa)

leftAssocB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [JoinKey f] (f a)
leftAssocB m fffa = applyB m fffa `validatedThen` \ffa -> applyB m ffa

rightAssocB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [JoinKey f] (f a)
rightAssocB m fffa =
  traverseDefault (applyB m) fffa `validatedThen` \ffa -> applyB m ffa

associativity :: (PTraversable f) => Join f -> f (f (f Int)) -> Maybe [JoinKey f]
associativity m fffa =
  case (,) <$> leftAssocB m fffa <*> rightAssocB m fffa of
    Success (leftFa, rightFa) -> if eqDefault leftFa rightFa then Just [] else Nothing
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
    keys1 = [minBound .. maxBound] :: [Key f]
    monoidCases = Map.fromList
      [ (key (Comp1 (void y <$ x)), monoidMult monDict xk yk)
        | xk <- keys1,
          let x = f1 ! fromEnum xk,
          yk <- keys1,
          let y = f1 ! fromEnum yk ]

_pure :: PTraversable f => Env f -> a -> f a
_pure env a = a <$ (_f1 env ! fromEnum uKey)
  where
    uKey = monoidUnit (_baseMonoid env)

runGen :: forall f r. (PTraversable f) => MonoidOn f -> Gen f r -> [(r, GenState f)]
runGen monDict mr = runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env = buildInitialEnv monDict

    f3 = _f3 env
    k3 = Vec.vec [minBound .. maxBound] :: Vec (Key (f :.: f :.: f))

    join0 = NM.empty
    blockade = maybe (error "should never happen?") (foldl' unionRel Map.empty) $ traverse newConstraint (Vec.zip f3 k3)
    newConstraint (fa, k) = foldMap (\blockKey -> Map.singleton blockKey (S1.singleton k)) <$> associativity join0 fa

    state0 :: GenState f
    state0 =
      GenState
        { _join = join0,
          _blockade = blockade
        }

_unkey1 :: PTraversable f => Env f -> Key f -> f Int
_unkey1 env k = _f1 env Vec.! fromEnum k

_unkey2 :: PTraversable f => Env f -> Key (f :.: f) -> f (f Int)
_unkey2 env k = _f2 env Vec.! fromEnum k

_unkey3 :: PTraversable f => Env f -> Key (f :.: f :.: f) -> f (f (f Int))
_unkey3 env k = _f3 env Vec.! fromEnum k

use :: (Functor f) => f Int -> Vec a -> f a
use template as = (as !) <$> template

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
      Just rhs' -> guard (eqDefault rhs rhs')
    let lhsKey = key lhs
        join2 = NM.insert (use rhs) lhsKey join1

    unkey3 <- asks _unkey3
    blockade <- gets _blockade

    -- update assocL
    let (blockedAssocs, blockade') = popRel lhsKey blockade
        newConstraint k3 = foldMap (\nextLhsKey -> singletonRel nextLhsKey k3) <$> associativity join2 (unkey3 k3)
    blockade'' <- case traverse newConstraint (S1.toList blockedAssocs) of
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
  let f1 = _f1 env
      u = _pure env
      ui = f1 ! fromEnum (key (u ()))
      uj = fmap (\i -> _length ui * i + i) ui
  entry (Comp1 (u ui)) uj

entryFUG :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Gen f ()
entryFUG = do
  env <- ask
  let f1 = _f1 env
      u = _pure env
      targets =
        [ fi | (i, fi) <- Vec.toList (Vec.indexed f1), i /= fromEnum (key (u ()))
        ]

      n = _length (u ())
      makeJuf :: f Int -> [f Int]
      makeJuf fi = traverseDefault select fi
        where
          m = _length fi
          select x = [y * m + x | y <- [0 .. n - 1]]
      makeJfu :: f Int -> [f Int]
      makeJfu = traverseDefault select
        where
          select x = [x * n + y | y <- [0 .. n - 1]]

  for_ targets $ \fi -> do
    juf <- choose $ makeJuf fi
    entry (Comp1 (u fi)) juf
    jfu <- choose $ makeJfu fi
    entry (Comp1 (u <$> fi)) jfu

guess :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => JoinKey f -> Gen f ()
guess lhsKey = do
  unkey1 <- asks _unkey1
  unkey2 <- asks _unkey2
  let lhs = Comp1 $ unkey2 lhsKey
      lhsVars = toVec lhs
  monoidCases <- asks _monoidCases
  rhs <- case Map.lookup lhsKey monoidCases of
    Nothing -> choose (enum1 lhsVars)
    Just rhsKey -> choose $ traverseDefault (const lhsVars) (unkey1 rhsKey)
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

-- unsafe access

(!) :: Vec a -> Int -> a
(!) = (Vec.!)

-- Relation data structure

type Rel k f = Map.Map k (S1.Set1 f)

singletonRel :: k -> Key f -> Rel k f
singletonRel k fKey = Map.singleton k (S1.singleton fKey)

unionRel :: (Ord k) => Rel k f -> Rel k f -> Rel k f
unionRel = Map.unionWith S1.union

popRel :: (Ord k) => k -> Rel k f -> (S1.Set1 f, Rel k f)
popRel k m = case Map.lookup k m of
  Nothing -> (S1.empty, m)
  Just s -> (s, Map.delete k m)

mostRelated :: (Ord k) => Rel k f -> Maybe k
mostRelated m
  | Map.null m = Nothing
  | otherwise = Just kTop
  where
    (kTop, _) = maximumBy (comparing (S1.size . snd)) $ Map.toList m
