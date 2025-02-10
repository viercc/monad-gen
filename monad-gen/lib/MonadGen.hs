{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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

    -- * Debug
    GenState (..),
    Gen,
    runGen,
    debugPrint,
    Join,
    Blockade,

    -- * Raw
    RawMonadData(..),
    Mop(..),
    genRaw
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

import MonoidGen (RawMonoidData(..))
import ApplicativeGen
import Isomorphism (Iso (..))
import Data.Equivalence.Monad

import MonadLaws
import qualified Data.Vector as V
import ModelFinder.Expr
import ModelFinder.Sig.Mono
import ModelFinder.Solver
import qualified Data.Array as Array

import Debug.Trace
import qualified Data.Vector.Unboxed as UV

import Data.Dependent.Sum (DSum(..))
import Data.Dependent.Map qualified as DMap
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.GADT.Show (GShow (..))
import Data.GADT.Compare
import Data.Type.Equality ((:~:)(..))
import Data.Constraint.Extras

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
      let assoc = flip all skolem3 $ checkAssoc (NM.unwrapNT join' . Comp1)
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

_pure :: PTraversable f => Env f -> a -> f a
_pure env = _applicativePure (_baseApplicative env)

runGen :: forall f r. (PTraversable f) => ApplicativeDict f -> Gen f r -> [(r, GenState f)]
runGen apDict mr = runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env = buildInitialEnv apDict

    f3 = _f3 env

    join0 = NM.empty
    blockade = maybe (error "should never happen?") (foldl' unionRel Map.empty) $ traverse newConstraint (V.indexed f3)
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
        newConstraint k = foldMap (\nextLhsKey -> singletonRel nextLhsKey k) <$> associativity join2 (f3 V.! k)
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
  rhs <- choose (enum1 (toList lhs))
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

-- Generate RawMonadData

data RawMonadData = RawMonadData {
    _baseRawApplicative :: RawApplicativeData
  , _mopTable :: Solution Mop
  }
  deriving (Show)

data Mop x where
  JShape :: !Int -> !(V.Vector Int) -> Mop Int
  JPos :: !Int -> !(V.Vector Int) -> Mop (V.Vector Int)

deriving instance Show (Mop x)
deriving instance Eq (Mop x)
deriving instance Ord (Mop x)

instance GShow Mop where gshowsPrec = showsPrec
instance GEq Mop where
  geq m1@JShape{} m2@JShape{} = guard (m1 == m2) *> Just Refl
  geq m1@JPos{} m2@JPos{} = guard (m1 == m2) *> Just Refl
  geq _ _ = Nothing

instance GCompare Mop where
  gcompare m1@JShape{} m2@JShape{} = genOrdering (compare m1 m2)
  gcompare m1@JPos{} m2@JPos{} = genOrdering (compare m1 m2)
  gcompare JShape{} JPos{} = GLT
  gcompare JPos{} JShape{} = GGT

instance (c Int, c (V.Vector Int)) => Has c Mop where
  has JShape{} body = body
  has JPos{} body = body

type Expr' = Expr Mop
type Model' = Model Mop
type Prop = Property Mop

jshape :: Expr' Int -> Expr' (V.Vector Int) -> Expr' Int
jshape = lift2 JShape

jpos :: Expr' Int -> Expr' (V.Vector Int) -> Expr' (V.Vector Int)
jpos = lift2 JPos

genRaw :: RawApplicativeData -> [RawMonadData]
genRaw rawAp = do
  let (model, props) = monadModel rawAp
  model' <- solve 10 model (Map.fromList (zip [0 :: Int ..] props))
  sol <- constraintToSolution model'
  pure $ RawMonadData{ _baseRawApplicative = rawAp, _mopTable = sol }

sumOf :: Foldable t => (a -> Int) -> t a -> Int
sumOf f = foldl' (\n a -> n + f a) 0

monadModel :: RawApplicativeData -> (Model', [Prop])
monadModel rawAp = (model, props)
  where
    sig = _signature rawAp
    len = (sig V.!)
    mon = _baseMonoid rawAp
    n = _monoidSize mon
    op x y = _multTable mon Array.! (x,y)
    leftTable = _leftFactorTable rawAp
    rightTable = _rightFactorTable rawAp

    ms = [0 .. n - 1]
    possibleLengths = Set.toList . Set.fromList . V.toList $ sig
    
    jshapeList = do
      x <- ms
      ys <- V.generateM (len x) (const ms)
      pure (JShape x ys :=> Set.fromList ms) 
    jposList = do
      x <- ms
      ys <- V.generateM (len x) (const ms)
      let ks = [0 .. sumOf len ys - 1]
          indicesList = do
            returnLen <- possibleLengths
            V.generateM returnLen (const ks)
      pure (JPos x ys :=> Set.fromList indicesList)
    
    model = Model $ DMap.fromList $ jshapeList ++ jposList
    
    props = knownFacts ++ posLenCondition ++ monadLawProps

    posLenCondition = do
      x <- ms
      ys <- V.generateM (len x) (const ms)
      pure $ do
        xy <- jshape (pure x) (pure ys)
        jpos (pure x) (pure ys) `satisfies` \indexVec -> V.length indexVec == len xy

    knownFacts = do
      x <- ms
      if len x > 0
        then ms >>= nonNullCase x
        else nullCase x
      where
        nullCase x = [knownShape, knownPos]
          where
            knownShape = jshape (pure x) (pure V.empty) `evaluatesTo` x
            knownPos = jpos (pure x) (pure V.empty) `evaluatesTo` V.empty
        nonNullCase x y = [knownShape, knownPos]
          where
            ys = V.replicate (len x) y
            knownShape = jshape (pure x) (pure ys) `evaluatesTo` op x y
            
            leftTab = leftTable Array.! (x,y)
            rightTab = rightTable Array.! (x,y)
            ixTable = V.zipWith (\i j -> i * len y + j) leftTab rightTab
            knownPos = jpos (pure x) (pure ys) `evaluatesTo` ixTable

    join' :: Int -> V.Vector Int -> V.Vector a -> Expr Mop (Maybe (Int, V.Vector a))
    join' x ys as = do
      (xy, pos) <- liftA2 (,) (jshape (pure x) (pure ys)) (jpos (pure x) (pure ys))
      pure $
        if len xy == V.length pos
          then Just (xy, V.backpermute as ( pos))
          else Nothing

    monadLawProps = do
      x <- ms
      ys <- V.generateM (len x) (const ms)
      zss <- V.mapM (\y -> V.generateM (len y) (const ms)) ( ys)
      assocLawProp x ys zss

    assocLawProp :: Int -> V.Vector Int -> V.Vector (V.Vector Int) -> [Property Mop]
    assocLawProp x ys zss = [shapeLaw, posLaw]
      where
        xyzPos :: V.Vector (V.Vector (V.Vector Int))
        xyzPos = indices3 . V.map (V.map (\z -> V.replicate (len z) ())) $ zss

        yzShapeExpr = V.imapM (\i zs -> jshape (pure (ys V.! i)) (pure zs)) zss
        zFlat = joinV zss

        shapeLaw =
          defined (join' x ys zFlat) $ \(xy, z') ->
             jshape (pure xy) (pure z') `equals` jshape (pure x) yzShapeExpr

        posLawLHS cont = do
          let zFlat' = V.zip zFlat (joinV xyzPos)
          defined (join' x ys zFlat') $ \(xy, zs') -> do
            let (zs, posZs) = V.unzip zs'
            defined (join' xy zs (joinV posZs)) $ \(_, pos_xy_z) ->
              cont pos_xy_z

        posLawRHS cont = do
          mInnerJoins <- runMaybeT . traverse MaybeT $
            V.zipWith3 join' ys zss (V.map joinV xyzPos)
          defined (pure mInnerJoins) $ \innerJoins -> do
            let (yzs, posYzs) = V.unzip innerJoins
            defined (join' x yzs (joinV posYzs)) $ \(_, pos_x_yz) ->
              cont pos_x_yz
        posLaw = posLawLHS $ \lhs -> posLawRHS $ \rhs -> pure $ PropBool (lhs == rhs)

joinV :: V.Vector (V.Vector a) -> V.Vector a
joinV = join

indices3 :: Traversable t => t (t (t a)) -> t (t (t Int))
indices3 = unComp1 . unComp1 . _indices . Comp1 . Comp1

defined :: Expr f (Maybe a) -> (a -> Property f) -> Property f
defined ma k = ma >>= maybe (pure $ PropBool False) k