{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
module MonadGen.CSP(
  genMonad,

  genMonadForPure,
  genMonadPureFirst,

  genMonadFromApplicative
) where

import Data.Traversable (for)
import Data.Functor ((<&>))

import Data.List ((!?))
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
import Data.PTraversable.Extra (skolem, skolem2, shapes)

import MonadData
import CSP
import qualified Data.NatMap as NM
import ApplicativeData (ApplicativeDict(..), ApplicativeData, makeApplicativeDict)
import Control.Monad (guard)

type Shape2 f = Shape (f :.: f)

data MonadOpVars f = MonadOpVars {
    shapeTable :: V.Vector (Shape f),
    unitVar :: VarName,
    joinVars :: Map.Map (Shape2 f) (VarName, V.Vector (VarName, VarName))
  }

-- 'depend' but out-of-range value is Never
dependIn :: VarName -> Int -> Int -> ConstraintM Int
dependIn var lo hi = depend var >>= \i ->
  if lo <= i && i < hi
    then pure i
    else never

type MonadProblem f = (MonadOpVars f, Variables, Constraint)

unitVarName :: VarName
unitVarName = "e"

bullVarName :: Int -> [Int] -> VarName
bullVarName s v = "b_" ++ ((s:v) >>= intEnc)
leftIxVarName, rightIxVarName :: Int -> [Int] -> Int -> [Char]
leftIxVarName s v i = "l_" ++ ((s:v) >>= intEnc) ++ "_" ++ show i
rightIxVarName s v i = "r_" ++ ((s:v) >>= intEnc) ++ "_" ++ show i


-- Encode Int to String. 'concatMap' is injective.
-- >>> intEnc <$> [0 .. 13]
-- ["0","1","2","3","4","5","6","7","8","9","+10","+11","+12","+13"]
-- >>> intEnc <$> [-1, -2 .. -13]
-- ["-1","-2","-3","-4","-5","-6","-7","-8","-9","--10","--11","--12","--13"]
intEnc :: Int -> String
intEnc i
  | i < 0 = '-' : enc' '-' (negate i)
  | otherwise = enc' '+' i
  where
    enc' c x =
      let s = show x
          n = length s
      in replicate (n - 1) c ++ s

makeMonadProblem :: forall f. PTraversable f => MonadProblem f
makeMonadProblem = (monadOpVars, allVarDefs, allConstraints)
  where
    tab = V.fromList $ List.sortOn length (V.toList skolem)
    itab = V.toList $ V.indexed tab
    sig = length <$> tab

    n = V.length tab
    maxLen = maximum (0 : V.toList sig)

    monadOpVars = MonadOpVars (Shape <$> tab)
      unitVarName
      joinVarsMap

    shapeMap = Map.fromList $ do
      (s,fx) <- itab
      fv <- traverse (const itab) fx
      let ff = Shape (Comp1 (snd <$> fv))
          v = fst <$> F.toList fv
      pure (ff, (s,v))

    joinVarsMap = mkVarNames <$> shapeMap
      where
        mkVarNames (s,v) = (bullVarName s v, lrIxVarNameVec s v)
        lrIxVarNameVec s v = V.generate maxLen $ \i -> (leftIxVarName s v i, rightIxVarName s v i)

    allVarDefs = Map.insert unitVarName (VarRange 0 n) $ joinVarDefs
    joinVarDefs = Map.fromList $ Map.elems shapeMap >>= mkVarDef
    mkVarDef (s,v) = bullVarDef ++ leftIxVarDefs ++ rightIxVarDefs
      where
        bullVarDef = [(bullVarName s v, VarRange 0 n)]
        -- An "invalid" call return 0, thus
        -- the range must be at least [0,1).
        leftLen = max 1 (sig V.! s)
        maxRightLen = maximum (1 : map (sig V.!) v)

        leftIxVarDefs =
          [(leftIxVarName s v i, VarRange 0 leftLen) | i <- [0 .. maxLen - 1]]
        rightIxVarDefs =
          [(rightIxVarName s v i, VarRange 0 maxRightLen) | i <- [0 .. maxLen - 1]]

    allConstraints = conjunct [
        conjunct (makeTypeConstraint <$> Map.elems shapeMap)
      , conjunct monadLaws
      ]

    makeTypeConstraint (s,v) = do
      s' <- depend bullSV
      let lenS' = sig V.! s'
          lenS = sig V.! s
          lenVmax = maximum (0 : fmap (sig V.!) v)
      conjunct $ do
        i <- [0 .. maxLen - 1]
        let il = leftIxVarName s v i
            ir = rightIxVarName s v i
            correctRange = dependIn il 0 lenS >>= \j ->
              ir %<. sig V.! (v !! j)
        if i < lenS'
          then [correctRange]
          else [il %==. 0 | lenS > 0] ++ [ir %==. 0 | lenVmax > 0] 
      where
        bullSV = bullVarName s v

    monadLaws = [ unitLaws, assocLaws ]
    -- monadLaws = []

    makeSVW :: [(Int, [Int], [[Int]], f (f (f Int)))]
    makeSVW = do
      (s, fx) <- itab
      fvf <- traverse (const itab) fx
      let ffx = snd <$> fvf
          v = map fst (F.toList fvf)
      ffwf <- traverse (traverse (const itab)) ffx
      let fff = fmap (fmap snd) ffwf
          w = map (map fst . F.toList) $ F.toList ffwf
      pure (s,v,w,fff)

    -- unit laws (1,2,4,5)
    --
    -- Shape unit laws:
    -- [law1] bull s (const e) == s
    -- [law2] bull e (const s) == s
    -- 
    -- Position unit laws:
    -- [law4] leftIx s (const e) i == i
    -- [law5] rightIx e (const s) i == i
    unitLaws = do
      (s, sn) <- forAll $ V.toList (V.indexed sig)
      e <- depend unitVarName
      let en = sig V.! e
          sBar = replicate en s
          eBar = replicate sn e
          posId i = conjunct
            [ leftIxVarName s eBar i %==. i,
              rightIxVarName e sBar i %==. i ]
      conjunct
        [ bullVarName s eBar %==. s,
          bullVarName e sBar %==. s,
          forAll [0 .. sn - 1] >>= posId ]

    dependPos s v i = do
      let lenS = sig V.! s
          varL = leftIxVarName s v i
          varR = rightIxVarName s v i
      l <- dependIn varL 0 lenS 
      r <- dependIn varR 0 (sig V.! (v !! l))
      pure (l,r)

    -- assoc laws (3,6,7,8)
    --
    -- Shape assoc law:
    -- [law3] bull s vw == bull sv (Δ s v w)
    --
    -- where
    --   sv = bull s v
    --   vw = \i -> bull (v i) (w i)
    --   Δ s v w = \j -> w (leftIx s v j) (rightIx s v j)
    -- 
    -- Position assoc law:
    --
    -- [law6] leftIx s vw i == leftIx s v (leftIx sv (Δ s v w) i)
    -- [law7] (\j k -> leftIx (v j) (w j) k) (leftIx s vw i) (rightIx s vw i)
    --          == rightIx s v (leftIx sv (Δ s v w) i)
    -- [law8] (\j k -> rightIx (v j) (w j) k) (leftIx s vw i) (rightIx s vw i)
    --          == rightIx sv (Δ s v w) i
    assocLaws = do
      (s,v,w,_) <- forAll makeSVW
      sv <- depend $ bullVarName s v
      let sv_len = sig V.! sv
      lr_s_v <- traverse (dependPos s v) [0 .. sv_len - 1]
      let l_s_v j = maybe (-1) fst $ lr_s_v !? j
          r_s_v j = maybe (-1) snd $ lr_s_v !? j
      let delta_w = lr_s_v <&> \(j1,j2) -> w !! j1 !! j2
      vw <- traverse (\(vi,wi) -> depend (bullVarName vi wi)) (zip v w)
      let s_vw_var = bullVarName s vw
          sv_w_var = bullVarName sv delta_w
      s_vw <- depend s_vw_var
      let svw_len = sig V.! s_vw
          ix_laws i = do
            let l_sv_w_var = leftIxVarName sv delta_w i
                r_sv_w_var = rightIxVarName sv delta_w i
            (l_s_vw, r_s_vw) <- dependPos s vw i
            let lr_var = leftIxVarName (v !! l_s_vw) (w !! l_s_vw) r_s_vw
                rr_var = rightIxVarName (v !! l_s_vw) (w !! l_s_vw) r_s_vw
            conjunct
              [ l_sv_w_var `satisfy` (\j -> l_s_v j == l_s_vw),
                functionEq r_s_v l_sv_w_var lr_var,
                rr_var %==% r_sv_w_var
              ]
      conjunct [sv_w_var %==. s_vw, forAll [0 .. svw_len - 1] >>= ix_laws]

solutionToMonad :: PTraversable f => MonadOpVars f -> Map VarName Int -> Maybe (MonadData f)
solutionToMonad vars solution = MonadData <$> pureShape <*> join_
  where
    tab = shapeTable vars
    pureShape = (tab V.!) <$> Map.lookup (unitVar vars) solution

    lhsList = V.toList (Comp1 <$> skolem2)
    join_ = NM.fromEntries <$> traverse makeDef lhsList

    makeDef ffi = do
      let ixss = map F.toList (F.toList (unComp1 ffi))
      (rhsShapeVar, ixVars) <- Map.lookup (Shape ffi) (joinVars vars)
      Shape rhs0 <- (tab V.!) <$> Map.lookup rhsShapeVar solution
      let varLookup i = do
            let (i1var,i2var) = ixVars V.! i
            i1 <- Map.lookup i1var solution
            i2 <- Map.lookup i2var solution
            ixss !? i1 >>= (!? i2)
      rhs <- traverse varLookup (indices rhs0)
      NM.makeEntry ffi rhs

solveMonadProblem :: PTraversable f => MonadProblem f -> IO [MonadData f]
solveMonadProblem (varNames, defs, con) = do
  solutions <- solveCSP defs con (Map.keysSet defs)
  for solutions $ \solution ->
    case solutionToMonad varNames solution of
      Just monadData -> pure monadData
      Nothing -> error "bad!?"

genMonad :: PTraversable f => IO [MonadData f]
genMonad = solveMonadProblem makeMonadProblem

-- "Per Pure" strategy
genMonadForPure :: forall f. PTraversable f => Shape f -> IO [MonadData f]
genMonadForPure = \pureShape -> solveMonadProblem (addPureDef pureShape mp0)
  where
    mp0 = makeMonadProblem @f

uniqBy :: (a -> a -> Ordering) -> [a] -> [a]
uniqBy cmp = map NE.head . NE.groupBy eq . List.sortBy cmp
  where
    eq x y = cmp x y == EQ

genMonadPureFirst :: PTraversable f => IO [MonadData f]
genMonadPureFirst = do
  let uniqueLenShapes = uniqBy (comparing length) shapes 
  -- mapM_ print $ Map.toList defs
  monadss <-
    for uniqueLenShapes $ \pureShape ->
      genMonadForPure (Shape pureShape)
  pure $ concat monadss

genMonadFromApplicative :: forall f. PTraversable f => ApplicativeData f -> IO [MonadData f]
genMonadFromApplicative = \apData -> solveMonadProblem (addApplicativeConstraint (makeApplicativeDict apData) mp0)
  where
    mp0 = makeMonadProblem @f

addPureDef :: PTraversable f => Shape f -> MonadProblem f -> MonadProblem f
addPureDef pureShape (varNames, defs, con) = (varNames, defs, con')
  where
    revmap = Map.fromList [ (s,i) | (i,s) <- V.toList (V.indexed (shapeTable varNames)) ]      
    pureShapeId = revmap Map.! pureShape
    con' = conjunct [unitVar varNames %==. pureShapeId, con] 

addPartialJoinDef :: PTraversable f => NM.NatMap (f :.: f) f -> MonadProblem f -> MonadProblem f
addPartialJoinDef nm (varNames, defs, con) = (varNames, defs, con')
  where
    revmap = Map.fromList [ (f,s) | (s,f) <- V.toList (V.indexed (shapeTable varNames)) ]
    rev = (revmap Map.!)
    rev2 ff = (s,v)
      where s = rev (Shape ff)
            v = rev . Shape <$> F.toList ff
    
    con' = conjunct [knownDefs, con]
    knownDefs = forAll (NM.getKeyValue <$> NM.toEntries nm) >>= knownDef
    knownDef (Shape lhs0, rhsVar) = conjunct (shapeDef : posDefs)
      where
        lhs = indices lhs0
        rhs = NM.unVar <$> rhsVar
        (s,v) = rev2 (unComp1 lhs)
        sv = rev (Shape rhs)
        shapeDef = bullVarName s v %==. sv

        lhsPosMap = Map.fromList
          [ (k, (i1,i2)) | (i1,subF) <- zip [0..] (F.toList (unComp1 lhs)), (i2,k) <- zip [0..] (F.toList subF) ]
        rhsPos = F.toList (imap (,) rhs)
        posDefs = rhsPos >>= posDef
        posDef (i,k) =
          let (i1,i2) = lhsPosMap Map.! k
          in [ leftIxVarName s v i %==. i1, rightIxVarName s v i %==. i2 ]

impossibleProblem :: MonadProblem f -> MonadProblem f
impossibleProblem (varNames, _, _) = (varNames, Map.empty, never)

addApplicativeConstraint :: PTraversable f => ApplicativeDict f -> MonadProblem f -> MonadProblem f
addApplicativeConstraint apDict =
    maybe impossibleProblem addPartialJoinDef partialJoin
     . addPureDef pureShape
  where
    pureShape = Shape (_applicativePure apDict ())
    partialJoin = applicativeToJoin apDict

applicativeToJoin :: (PTraversable f) => ApplicativeDict f -> Maybe (NM.NatMap (f :.: f) f)
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
