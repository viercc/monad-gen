{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
module MonadGen.CSP(
  genMonad,

  genMonadForPure,
  genMonadPureFirst,

  genMonadFromApplicative
) where

import Data.Traversable (for)

import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NE
import Data.Ord (comparing)
import GHC.Generics ((:.:) (..))

import Data.PTraversable
import Data.FunctorShape
import Data.Traversable.Extra (indices, imap)
import Data.PTraversable.Extra (skolem, skolem2, shapes, skolem3)

import MonadData
import CSP
import qualified Data.NatMap as NM
import ApplicativeData (ApplicativeDict(..))
import Control.Monad (guard)
import Data.Functor (void)
import qualified Data.Set as Set
import GHC.Stack.Types (HasCallStack)

type Shape2 f = Shape (f :.: f)
type Shape3 f = Shape ((f :.: f) :.: f)

data MonadOps f =
  -- These define Monad operations
    -- Shape of the pure :: Identity ~> f
    Unit
    -- Shape part of the join :: (f :.: f) ~> f
  | Bull (Shape2 f)
    -- Position part of the join :: (f :.: f) ~> f
  | Pos (Shape2 f) Int

  {-

  Note about how `Pos` is implemented:

  The precise type of Pos depends on value of variable Bull take.
  If `Bull ff` take a value in `rhs :: f _`, the type of `Pos ff` would be
  `Pos ff :: { i :: Int | 0 <= i && i < length rhs } -> MonadOps f`.
  
  This precise type is not something possible to state; thus this module
  uses alternative

  `Pos ff :: { i :: Int | 0 <= i && i < maxRhsLen } -> MonadOps f`

  wher `maxRhsLen` is a maximum value of `length f` where `f` varies among all
  `f ()`.

  the "precise" type is represented by
  - Define `Pos ff i %==. 0` for any "undefined" `i`
  - Not reference `Pos ff i` for `i` making it undefined
    in other places
  
  -}

  -- Temporary variables to state associativity law
    -- Shape part of the one side of associativity law (join :: (f :.: f :.: f) ~> (f :.: f) 
  | BullOuter (Shape3 f)
    -- Shape part of the one side of associativity law (fmap join :: (f :.: f :.: f) ~> (f :.: f) 
  | BullInner (Shape3 f)
    -- Shape part of the associativity law :: (f :.: f :.: f) ~> f
  | Bull3 (Shape3 f)
    -- Length cache of Bull3
  | Bull3Len (Shape3 f)
    -- Position part of the one side of associativity law (join :: (f :.: f :.: f) ~> (f :.: f) 
  | PosOuter (Shape3 f) Int
    -- Position part of the one side of associativity law (fmap join :: (f :.: f :.: f) ~> (f :.: f) 
  | PosInner (Shape3 f) Int
    -- Position part of the associativity law :: (f :.: f :.: f) ~> f
  | Pos3  (Shape3 f) Int

deriving instance (forall a. Eq a => Eq (f a)) => Eq (MonadOps f)
deriving instance (forall a. Eq a => Eq (f a), forall a. Ord a => Ord (f a)) => Ord (MonadOps f)
deriving instance (forall a. Show a => Show (f a)) => Show (MonadOps f)

type MonadProblem f = (V.Vector (f Int), Variables (MonadOps f), Constraint (MonadOps f))

dependIn :: v -> Int -> Int -> ConstraintM v Int
dependIn v lo hi = do
  k <- depend v
  if lo <= k && k < hi
    then pure k
    else never

(!) :: (HasCallStack, Show a) => V.Vector a -> Int -> a
vec ! i = case vec V.!? i of
  Nothing -> error $ "index out of bounds " ++ show (vec, i)
  Just a -> a

makeMonadProblem :: forall f. (PTraversable f, forall a. Show a => Show (f a)) => MonadProblem f
makeMonadProblem = (f1, allVarDefs, allConstraints)
  where
    f1 :: V.Vector (f Int)
    f1 = skolem
    f2 :: V.Vector (f (f Int))
    f2 = skolem2
    f3 :: V.Vector (f (f (f Int)))
    f3 = skolem3

    -- n = total number of shapes
    n = V.length f1
    -- n2 = total number of twice-nested shapes
    n2 = V.length f2
    -- maxRhsLen = max possible index for Pos and Pos3 variables.
    maxRhsLen = maximum (0 : map length (V.toList f1))
    minRhsLen = minimum (maxRhsLen : map length (V.toList f1))

    revmap2 :: forall b. f (f b) -> Int
    revmap2 = (m Map.!) . Shape . Comp1
      where
        m = Map.fromList [ (Shape (Comp1 ff), i) | (i,ff) <- V.toList (V.indexed f2) ]

    allVarDefs = Map.unions
      [ Map.singleton Unit (VarRange 0 n)
      , joinVarDefs
      , tmpVarDefs
      ]
    joinVarDefs = Map.fromList $ V.toList f2 >>= mkVarDef
    mkVarDef ffx = bullVarDef ++ posVarDefs
      where
        ff = Shape (Comp1 ffx)
        bullVarDef = [(Bull ff, VarRange 0 n)]
        lhsLen = lengthShape ff
        posVarDefs = [(Pos ff i, VarRange 0 (max 1 lhsLen)) | i <- [0 .. maxRhsLen - 1]]

    tmpVarDefs = Map.fromList $ V.toList f3 >>= mkVarDefTmp
    mkVarDefTmp fffx = bullVarDef ++ posVarDefs
      where
        fff = Shape (Comp1 (Comp1 fffx))
        lhsLen = lengthShape fff
        bullVarDef = [
            (Bull3 fff, VarRange 0 n),
            (Bull3Len fff, VarRange minRhsLen (maxRhsLen+1)),
            (BullOuter fff, VarRange 0 n2),
            (BullInner fff, VarRange 0 n2)
          ]
        posVarDefs =
          [ (Pos3 fff i, VarRange 0 (max 1 lhsLen)) | i <- [0 .. maxRhsLen - 1]] ++
          [ (PosOuter fff i, VarRange 0 (max 1 lhsLen)) | i <- [0 .. maxRhsLen * maxRhsLen - 1]] ++
          [ (PosInner fff i, VarRange 0 (max 1 lhsLen)) | i <- [0 .. maxRhsLen * maxRhsLen - 1]]

    allConstraints = conjunct [
        conjunct (invalidPositions <$> F.toList f2)
      , conjunct (invalidPositions3 <$> F.toList f3)
      , bull3LenCache

      , unitLaws
      , assocLaw
      ]

    -- define arbitrary value for "invalid" @Pos ff i@
    invalidPositions ffx = do
      let ff = Shape (Comp1 ffx)
      f <- (f1 V.!) <$> depend (Bull ff)
      let rhsLen = length f
          lhsLen = lengthShape ff
      i <- forAll [0 .. maxRhsLen - 1]
      if i < rhsLen
        then Pos ff i %<. lhsLen
        else Pos ff i %==. 0

    invalidPositions3 fffx = conjunct [outerPosRange, innerPosRange, pos3Range]
      where
        fff = Shape (Comp1 (Comp1 fffx))
        lhsLen = lengthShape fff
        outerPosRange = do
          ff <- (f2 V.!) <$> depend (BullOuter fff)
          let rhsLen = length (Comp1 ff)
          i <- forAll [0 .. maxRhsLen * maxRhsLen - 1]
          if i < rhsLen
            then PosOuter fff i %<. lhsLen
            else PosOuter fff i %==. 0
        
        innerPosRange = do
          ff <- (f2 V.!) <$> depend (BullInner fff)
          let rhsLen = length (Comp1 ff)
          i <- forAll [0 .. maxRhsLen * maxRhsLen - 1]
          if i < rhsLen
            then PosInner fff i %<. lhsLen
            else PosInner fff i %==. 0
        
        pos3Range = do
          rhsLen <- depend (Bull3Len fff)
          i <- forAll [0 .. maxRhsLen - 1]
          if i < rhsLen
            then Pos3 fff i %<. lhsLen
            else Pos3 fff i %==. 0

    bull3LenCache = do
      fffx <- forAll (V.toList f3)
      let fff = Shape . Comp1 . Comp1 $ fffx 
      functionEq (\fId -> length (f1 V.! fId)) (Bull3 fff) (Bull3Len fff)

    -- unit laws
    unitLaws = do
      (fId,f) <- forAll (V.toList (V.indexed f1))
      e <- (f1 V.!) <$> depend Unit
      let ne = length e
          nf = length f
      {-

      pure x = (x <$ e)
      fe = Comp1 (fmap pure f)
         = Comp1 $ F (E 0 0 ...(ne times)) (E 1 1 ...) (E 2 2 ...)
      ef = Comp1 (pure f)
         = Comp1 $ E (F 0 1 2 ... (nf-1)) (F 0 1 2 ... (nf-1)) ...(ne times)...

      feVec = toList fe
      efVec = toList ef

      ∀　i. (0 <= i < nf) --> Pos (Shape fe) i %==. feVec !! i
      ∀　i. (0 <= i < nf) --> Pos (Shape ef) i %==. efVec !! i

      -}
      let fe = Shape (Comp1 (e <$ f))
          ef = Shape (Comp1 (f <$ e))

          posProps i =
            [ Pos fe i `satisfy` \j -> ne == 0 || j `div` ne == i,
              Pos ef i `satisfy` \j -> nf == 0 || j `mod` nf == i ]
      conjunct $
        [ Bull fe %==. fId,
          Bull ef %==. fId ] ++
        ([0 .. nf - 1] >>= posProps)

    dependShape :: forall b. f (f b) -> ConstraintM (MonadOps f) (f ())
    dependShape ffb = void . (f1 V.!) <$> depend (Bull (Shape (Comp1 ffb)))

    dependJoin :: forall b. Show b => f (f b) -> ConstraintM (MonadOps f) (f b)
    dependJoin ffb = do
      let ffb' = Comp1 ffb
          bTable = V.fromList (F.toList ffb')
          lhsLen = length ffb'
      fi <- (f1 V.!) <$> depend (Bull (Shape ffb'))
      traverse (\i -> (bTable V.!) <$> dependIn (Pos (Shape ffb') i) 0 lhsLen) fi

    -- assoc laws
    assocLaw = do
      fffx <- forAll $ V.toList skolem3
      conjunct [assocLawOuter fffx, assocLawInner fffx]
    
    assocLawOuter fffx = conjunct [outer1, outer2Bull, outer2Pos]
      where
        fff = Shape . Comp1 . Comp1 $ fffx
        outer1 = do
          outerJoin <- dependJoin fffx
          let shapeId = revmap2 outerJoin
              rhsLen = length (Comp1 outerJoin)
              posmap = vecFromFF outerJoin
              posDef i = PosOuter fff i %==. (posmap ! i)
          conjunct $
            (BullOuter fff %==. shapeId) : fmap posDef [0 .. rhsLen - 1]
        outer2Bull = do
          ff <- Shape . Comp1 . (f2 V.!) <$> depend (BullOuter fff)
          Bull ff %==% Bull3 fff
        outer2Pos = do
          ff <- Shape . Comp1 . (f2 V.!) <$> depend (BullOuter fff)
          rhsLen <- depend (Bull3Len fff)
          i <- forAll [0 .. rhsLen - 1]
          j <- depend (Pos ff i)
          PosOuter fff j %==% Pos3 fff i
    
    assocLawInner fffx = conjunct [inner1, inner2Bull, inner2Pos]
      where
        fff = Shape . Comp1 . Comp1 $ fffx
        subJoinShapes = fmap (Shape . Comp1) . V.fromList . F.toList $ fffx
        shiftAmount = V.scanl' (\acc s -> acc + lengthShape s) 0 subJoinShapes
        inner1 = do
          innerJoinShape <- traverse dependShape fffx
          let shapeId = revmap2 innerJoinShape
              rhsLen = length (Comp1 innerJoinShape)
              divider = vecFromFF $ path2 innerJoinShape
              posDef j =
                let (j1,j2) = divider ! j
                in functionEq ((shiftAmount ! j1) +) (Pos (subJoinShapes ! j1) j2) (PosInner fff j)
          conjunct $ (BullInner fff %==. shapeId) : fmap posDef [0 .. rhsLen - 1]
        inner2Bull = do
          ff <- Shape . Comp1 . (f2 V.!) <$> depend (BullInner fff)
          Bull ff %==% Bull3 fff
        inner2Pos = do
          ff <- Shape . Comp1 . (f2 V.!) <$> depend (BullInner fff)
          rhsLen <- depend (Bull3Len fff)
          i <- forAll [0 .. rhsLen - 1]
          j <- depend (Pos ff i)
          PosInner fff j %==% Pos3 fff i

    vecFromFF :: forall b. f (f b) -> V.Vector b
    vecFromFF = V.fromList . F.toList . Comp1

    path2 :: forall b. f (f b) -> f (f (Int,Int))
    path2 = imap (\k1 fb -> imap (\k2 _ -> (k1,k2)) fb)

solutionToMonad :: PTraversable f => V.Vector (f Int) -> Map (MonadOps f) Int -> Maybe (MonadData f)
solutionToMonad tab solution = MonadData <$> pureShape <*> join_
  where
    pureShape = Shape . (tab V.!) <$> Map.lookup Unit solution
    lhsList = V.toList (Comp1 <$> skolem2)
    join_ = NM.fromEntries <$> traverse joinDef lhsList
    joinDef ffi = do
      f <- (tab V.!) <$> Map.lookup (Bull (Shape ffi)) solution
      let p i = Map.lookup (Pos (Shape ffi) i) solution
      fi <- traverse p (indices f)
      NM.makeEntry ffi fi

solveMonadProblem :: (PTraversable f, forall a. Show a => Show (f a)) => MonadProblem f -> IO [MonadData f]
solveMonadProblem (tab, defs, con) = do
  solutions <- solveCSP defs con (Set.filter neededVar $ Map.keysSet defs)
  for solutions $ \solution ->
    case solutionToMonad tab solution of
      Just monadData -> pure monadData
      Nothing -> error "bad!?"
  where
    neededVar var = case var of
      Unit -> True
      Bull _ -> True
      Pos _ _ -> True
      _ -> False

genMonad :: (PTraversable f, forall a. Show a => Show (f a)) => IO [MonadData f]
genMonad = solveMonadProblem makeMonadProblem

-- "Per Pure" strategy
genMonadForPure :: forall f. (PTraversable f, forall a. Show a => Show (f a)) => Shape f -> IO [MonadData f]
genMonadForPure = \pureShape -> solveMonadProblem (addPureDef pureShape mp0)
  where
    mp0 = makeMonadProblem @f

uniqBy :: (a -> a -> Ordering) -> [a] -> [a]
uniqBy cmp = map NE.head . NE.groupBy eq . List.sortBy cmp
  where
    eq x y = cmp x y == EQ

genMonadPureFirst :: (PTraversable f, forall a. Show a => Show (f a)) => IO [MonadData f]
genMonadPureFirst = do
  let uniqueLenShapes = uniqBy (comparing length) shapes
  -- mapM_ print $ Map.toList defs
  monadss <-
    for uniqueLenShapes $ \pureShape ->
      genMonadForPure (Shape pureShape)
  pure $ concat monadss

genMonadFromApplicative :: forall f. (PTraversable f, forall a. Show a => Show (f a)) => ApplicativeDict f -> IO [MonadData f]
genMonadFromApplicative = \apDict -> solveMonadProblem (addApplicativeConstraint apDict mp0)
  where
    mp0 = makeMonadProblem @f

addPureDef :: (PTraversable f, forall a. Show a => Show (f a)) => Shape f -> MonadProblem f -> MonadProblem f
addPureDef pureShape (tab, defs, con) = (tab, defs', con')
  where
    revmap = Map.fromList [ (Shape s,i) | (i,s) <- V.toList (V.indexed tab) ]
    pureShapeId = revmap Map.! pureShape
    (defs', con') = assume (Map.singleton Unit pureShapeId) (defs, con)

addPartialJoinDef :: PTraversable f => NM.NatMap (f :.: f) f -> MonadProblem f -> MonadProblem f
addPartialJoinDef nm (tab, defs, con) = (tab, defs', con')
  where
    revmap = Map.fromList [ (Shape s,i) | (i,s) <- V.toList (V.indexed tab) ]
    rev = (revmap Map.!)

    (defs', con') = assume (Map.fromList knownDefs) (defs, con)
    knownDefs = NM.toEntries nm >>= knownDef . NM.getKeyValue
    knownDef (lhs, rhsVar) = shapeDef : posDefs
      where
        rhs = NM.unVar <$> rhsVar
        shapeDef = (Bull lhs, rev (Shape rhs))

        posDefs = posDef <$> zip [0..] (F.toList rhs)
        posDef (i,k) = (Pos lhs i, k)

impossibleProblem :: MonadProblem f -> MonadProblem f
impossibleProblem (varNames, _, _) = (varNames, Map.empty, never)

addApplicativeConstraint :: (PTraversable f, forall a. Show a => Show (f a)) => ApplicativeDict f -> MonadProblem f -> MonadProblem f
addApplicativeConstraint apDict =
    maybe impossibleProblem addPartialJoinDef partialJoin
     . addPureDef pureShape
  where
    pureShape = Shape (_applicativePure apDict ())
    partialJoin = applicativeToJoin apDict

applicativeToJoin :: (PTraversable f, forall a. Show a => Show (f a)) => ApplicativeDict f -> Maybe (NM.NatMap (f :.: f) f)
applicativeToJoin apDict = guard isFeasible *> joinMap
  where
    f1 = skolem
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

mapFromListUnique :: (Ord k, Eq v) => [(k,v)] -> Maybe (Map.Map k v)
mapFromListUnique = F.foldlM step Map.empty
  where
    step m (k,v) = Map.alterF (checkedInsert v) k m
    checkedInsert newV old = case old of
      Nothing -> Just (Just newV)
      Just oldV -> old <$ guard (newV == oldV)
