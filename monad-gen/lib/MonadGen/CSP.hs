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
import ApplicativeData (ApplicativeDict(..), ApplicativeData, makeApplicativeDict)
import Control.Monad (guard)
import Data.Functor (void)
import Debug.Trace
import qualified Data.Set as Set

type Shape2 f = Shape (f :.: f)
type Shape3 f = Shape ((f :.: f) :.: f)

data MonadOps f =
    Unit
  | Bull (Shape2 f)
  | Pos (Shape2 f) Int

  | Bull3 (Shape3 f)
  | Pos3  (Shape3 f) Int

deriving instance (forall a. Eq a => Eq (f a)) => Eq (MonadOps f)
deriving instance (forall a. Eq a => Eq (f a), forall a. Ord a => Ord (f a)) => Ord (MonadOps f)
deriving instance (forall a. Show a => Show (f a)) => Show (MonadOps f)

type MonadProblem f = (V.Vector (f Int), Variables (MonadOps f), Constraint (MonadOps f))


makeMonadProblem :: forall f. (PTraversable f, forall a. Show a => Show (f a)) => MonadProblem f
makeMonadProblem = (f1, allVarDefs, allConstraints)
  where
    f1 = skolem
    f2 = skolem2
    f3 = skolem3

    n = V.length f1
    maxRhsLen = maximum (0 : map length (V.toList f1))

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
        posVarDefs = [(Pos ff i, VarRange 0 lhsLen) | i <- [0 .. maxRhsLen - 1]]
    tmpVarDefs = Map.fromList $ V.toList f3 >>= mkVarDefTmp
    mkVarDefTmp fffx = bullVarDef ++ posVarDefs
      where
        fff = Shape (Comp1 (Comp1 fffx))
        lhsLen = lengthShape fff
        bullVarDef = [ (Bull3 fff, VarRange 0 n) ]
        posVarDefs = [ (Pos3 fff i, VarRange 0 lhsLen) | i <- [0 .. maxRhsLen - 1]]

    allConstraints = conjunct [
        conjunct (invalidPositions <$> F.toList f2)
      , conjunct (invalidPositions3 <$> F.toList f3)

      , unitLaws
      , assocShapeLaw
      , assocPosLaw
      ]

    -- define arbitrary value for "invalid" @Pos ff i@
    invalidPositions ffx = do
      let ff = Shape (Comp1 ffx)
      f <- (f1 V.!) <$> depend (Bull ff)
      i <- forAll [length f .. maxRhsLen - 1]
      Pos ff i %==. 0
    
    invalidPositions3 fffx = do
      let fff = Shape (Comp1 (Comp1 fffx))
      f <- (f1 V.!) <$> depend (Bull3 fff)
      i <- forAll [length f .. maxRhsLen - 1]
      Pos3 fff i %==. 0
    -- unit laws
    unitLaws = do
      (fId,f) <- forAll (V.toList (V.indexed f1))
      e <- (f1 V.!) <$> depend Unit
      let fe = Shape (Comp1 (e <$ f))
          ef = Shape (Comp1 (f <$ e))

          ne = length e
          nf = length f

          posProps i =
            [ Pos fe i `satisfy` \j -> ne == 0 || j `div` ne == i,
              Pos ef i `satisfy` \j -> ne == 0 || j `mod` ne == i ]
      conjunct $
        [ Bull fe %==. fId,
          Bull ef %==. fId ] ++
        ([0 .. nf - 1] >>= posProps)

    dependShape :: forall b. f (f b) -> ConstraintM (MonadOps f) (f ())
    dependShape ffb = void . (f1 V.!) <$> depend (Bull (Shape (Comp1 ffb)))

    dependJoin :: forall b. f (f b) -> ConstraintM (MonadOps f) (f b)
    dependJoin ffb = do
      let ffb' = Comp1 ffb
          bTable = V.fromList (F.toList ffb')
      fi <- (f1 V.!) <$> depend (Bull (Shape ffb'))
      traverse (\i -> (bTable V.!) <$> depend (Pos (Shape ffb') i)) fi

    -- assoc laws
    assocShapeLaw = do
      fffx <- forAll $ V.toList skolem3
      let tmpBull = Bull3 (Shape (Comp1 (Comp1 fffx)))
          outerDef = do
            outerJoin <- dependJoin fffx
            Bull (Shape (Comp1 outerJoin)) %==% tmpBull
          innerDef = do
            innerJoinShape <- traverse dependShape fffx
            Bull (Shape (Comp1 innerJoinShape)) %==% tmpBull
      conjunct [outerDef, innerDef]
    
    vecFromFF :: forall b. f (f b) -> V.Vector b
    vecFromFF = V.fromList . F.toList . Comp1

    path2 :: forall b. f (f b) -> f (f (Int,Int))
    path2 = imap (\k1 fb -> imap (\k2 _ -> (k1,k2)) fb)

    assocPosLaw = do
      fffx <- forAll $ V.toList skolem3
      conjunct [assocPosLawOuter fffx, assocPosLawInner fffx]

    assocPosLawOuter fffx = do
      outerJoin <- dependJoin fffx
      let posMap = vecFromFF outerJoin
      tmpShape <- (f1 V.!) <$> depend (Bull3 fff)
      i <- forAll [0 .. length tmpShape - 1]
      functionEq (posMap V.!) (Pos (Shape (Comp1 outerJoin)) i) (Pos3 fff i)
      where
        fff = Shape (Comp1 (Comp1 fffx))
    
    assocPosLawInner fffx = do
      innerJoinShape <- traverse dependShape fffx
      let divider = vecFromFF $ path2 innerJoinShape
      tmpShape <- (f1 V.!) <$> depend (Bull3 fff)
      i <- forAll [0 .. length tmpShape - 1]
      (j1,j2) <- (divider V.!) <$> depend (Pos (Shape (Comp1 innerJoinShape)) i)
      functionEq (shiftAmount j1 +) (Pos (subJoinShapes V.! j1) j2) (Pos3 fff i)
      where
        fff = Shape (Comp1 (Comp1 fffx))
        subJoinShapes = fmap (Shape . Comp1) . V.fromList . F.toList $ fffx
        shiftAmount j1 = sum . map (length . Comp1) . take j1 . F.toList $ fffx

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

genMonadFromApplicative :: forall f. (PTraversable f, forall a. Show a => Show (f a)) => ApplicativeData f -> IO [MonadData f]
genMonadFromApplicative = \apData -> solveMonadProblem (addApplicativeConstraint (makeApplicativeDict apData) mp0)
  where
    mp0 = makeMonadProblem @f

addPureDef :: (PTraversable f, forall a. Show a => Show (f a)) => Shape f -> MonadProblem f -> MonadProblem f
addPureDef pureShape (tab, defs, con) = (tab, defs, con')
  where
    revmap = Map.fromList [ (Shape s,i) | (i,s) <- V.toList (V.indexed tab) ]
    pureShapeId = revmap Map.! pureShape
    con' = conjunct [Unit %==. pureShapeId, con] 

addPartialJoinDef :: PTraversable f => NM.NatMap (f :.: f) f -> MonadProblem f -> MonadProblem f
addPartialJoinDef nm (tab, defs, con) = (tab, defs, con')
  where
    revmap = Map.fromList [ (Shape s,i) | (i,s) <- V.toList (V.indexed tab) ]
    rev = (revmap Map.!)
    
    con' = conjunct [knownDefs, con]
    knownDefs = forAll (NM.getKeyValue <$> NM.toEntries nm) >>= knownDef
    knownDef (lhs, rhsVar) = conjunct (shapeDef : posDefs)
      where
        rhs = NM.unVar <$> rhsVar
        shapeDef = Bull lhs %==. rev (Shape rhs)

        posDefs = posDef <$> zip [0..] (F.toList rhs)
        posDef (i,k) = Pos lhs i %==. k

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
