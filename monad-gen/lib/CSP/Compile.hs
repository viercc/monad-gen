{-# LANGUAGE DeriveTraversable #-}
module CSP.Compile(
  -- * Run the solver
  solveCSP,

  -- * Test and Debug
  solveCSPBruteForce,
  isValidAssignment,
  isValidAssignmentAtom,

  -- * Finer control of solving process
  findOneSolution,
  excludeSolution,
) where

import Control.Exception (assert)
import Data.Foldable (for_)
import GHC.Stack.Types (HasCallStack)
import Data.Map.Strict (Map)
import qualified Data.IntervalSet as IS

import Control.Monad.SAT (SAT, Neg (..), Lit)
import qualified Control.Monad.SAT as SAT
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Strict as SV

import Data.Set (Set)
import Data.Functor.Compose (Compose(..))
import Control.Monad (guard)

import CSP.Constraint
import CSP.SATUtil

solveCSP :: (Ord v, Show v) => Variables v -> Constraint v -> Set v -> IO [Map v Int]
solveCSP vars constraint visibleVars = runIterative $ do
  let litCount (VarRange lo hi) = max 0 (hi - lo - 1)
  debug   "INFO: instanting input problem"
  debug $ "INFO: #vars = " ++ show (Map.size vars)
  debug $ "INFO: #model_lits = " ++ show (sum $ litCount <$> Map.elems vars)
  env <- instantiateVars vars
  debug "INFO: adding constraints"
  addProp $ compileConstraint env constraint
  -- liftIO $ putStrLn "INFO: simplifying"
  -- simplify
  printStat
  debug "INFO: initialization done"
  pure (findOneSolution env visibleVars, excludeSolution env)

solveCSPBruteForce :: (Ord v, Show v) => Variables v -> Constraint v -> Set v -> [Map v Int]
solveCSPBruteForce vars con visibleVars = do
  assignment <- traverse (\(VarRange lo hi) -> [lo .. hi - 1]) vars
  guard $ isValidAssignment assignment con
  pure $ Map.restrictKeys assignment visibleVars

isValidAssignment :: (Ord v, Show v) => Map v Int -> Constraint v -> Bool
isValidAssignment env con = case con of
  Never -> False
  Pure atom -> isValidAssignmentAtom env atom
  Conjunct cons -> all (isValidAssignment env) cons
  Dependent varX cont -> justTrue $ isValidAssignment env . cont <$> Map.lookup varX env
  where
    justTrue = (== Just True)

isValidAssignmentAtom :: (Ord v, Show v) => Map v Int -> ConstraintAtom v -> Bool
isValidAssignmentAtom env con = case con of
  VarImmLt var k -> justTrue $ (< k) <$> lup var
  VarImmEq var k -> justTrue $ (k ==) <$> lup var
  VarImmNe var k -> justTrue $ (k /=) <$> lup var
  VarPred var cond -> justTrue $ cond <$> lup var
  VarVarEq varX varY -> justTrue $ (==) <$> lup varX <*> lup varY
  VarVarNe varX varY -> justTrue $ (/=) <$> lup varX <*> lup varY
  VarVarLe varX varY -> justTrue $ (<=) <$> lup varX <*> lup varY
  FunVarEq f varX varY -> justTrue $ (\x y -> f x == y) <$> lup varX <*> lup varY
  where
    lup = flip Map.lookup env
    justTrue = (== Just True)

-- * Compilation to SAT

data Bundle a = Bundle {
    _bundleLo :: !Int,
    _bundleHi :: !Int,
    _litvec :: !(SV.Vector a)
  }
  deriving (Functor, Foldable, Traversable)

type LitBundle s = Bundle (Lit s)

type Env v s = Map v (LitBundle s)

bundleToInt :: Bundle Bool -> Int
bundleToInt (Bundle lo _ vec) = lo + length (filter not $ SV.toList vec)

getBundle :: (Ord v, Show v, HasCallStack) => Env v s -> v -> LitBundle s
getBundle env name = Map.findWithDefault err name env
  where
    err = error $ "Variable not found: " ++ show name

lessThan' :: LitBundle s -> Int -> Lit' s
lessThan' (Bundle lo hi vec) k
  | k <= lo = LitFalse
  | k >= hi = LitTrue
  | otherwise = LitHit $ vec SV.! (k - lo - 1)

lessThan :: LitBundle s -> Int -> Prop s
lessThan x k = lit' (lessThan' x k)

geqThan :: LitBundle s -> Int -> Prop s
geqThan x k = lit' (neg (lessThan' x k))

instantiateVars :: Variables v -> SAT s (Env v s)
instantiateVars = traverse instantiateVar

{-

Order encoding: an integer variable x (0 <= x < n) is encoded by
(n - 1) literals

  x_1, x_2, ..., x_{n-1}

with constraints

  (x_1 → x_2) ∧ (x_2 → x_3) ∧ ... ∧ (x_{n-2} → x_{n-1})

Each x_k represent (x < i). A vector (x_1, x_2, ..., x_{n-1})
take n patterns total, each representing x = 0, x = 1, ..., x = n-1.

x,   x_1, x_2, ..., x_{n-2}, x_{n-1}
0,   1,   1,   ..., 1,       1
1,   0,   1,   ..., 1,       1
2,   0,   0,   ..., 1,       1
︙
n-2, 0,   0,   ..., 0,       1
n-1, 0,   0,   ..., 0,       0

-}
instantiateVar :: VarRange -> SAT s (LitBundle s)
instantiateVar (VarRange lo hi)
  | n <= 0 = SAT.addClause [] >> pure (Bundle lo lo SV.empty)
             -- ^ Unsatisfiable
  | n == 1 = pure (Bundle lo hi SV.empty)
             -- ^ The variable is actually constant (x == lo): no literals needed
  | otherwise = assert (n > 1) $ do
      -- instantiate x_i for all (1 <= i < n)
      lits <- SV.replicateM (n - 1) SAT.newLit
      -- (x_i → x_{i+1}) for all i defined
      for_ (SV.zip lits (SV.drop 1 lits)) $ \(xi, xi') ->
        SAT.addClause [neg xi, xi']
      pure (Bundle lo hi lits)
  where
    n = hi - lo

------------------

-- | Translate 'Constraint' to 'Prop'.
compileConstraint :: (Ord v, Show v, HasCallStack) => Env v s -> Constraint v -> Prop s
compileConstraint env con  = case con of
  Never -> false
  Pure c -> compileConstraintAtom env c
  Conjunct cons -> andProp (compileConstraint env <$> cons)
  Dependent varName subCon -> dependent (getBundle env varName) (compileConstraint env . subCon)

compileConstraintAtom :: (Ord v, Show v, HasCallStack) => Env v s -> ConstraintAtom v -> Prop s
compileConstraintAtom env con  = case con of
  VarImmLt varName k -> lessThan (getBundle env varName) k
  VarImmEq varName k -> varEq (getBundle env varName) k
  VarImmNe varName k -> varNe (getBundle env varName) k
  VarPred varName cond -> varPred (getBundle env varName) cond
  VarVarEq varX varY -> varvarEq (getBundle env varX) (getBundle env varY)
  VarVarNe varX varY -> dependent (getBundle env varX) (varNe (getBundle env varY))
  VarVarLe varX varY -> varvarLe (getBundle env varX) (getBundle env varY)
  FunVarEq f varX varY -> funVarEq f (getBundle env varX) (getBundle env varY)

varEq :: LitBundle s -> Int -> Prop s
varEq x k = geqThan x k /\ lessThan x (k + 1)

varNe :: LitBundle s -> Int -> Prop s
varNe x k = lessThan x k \/ geqThan x (k + 1)

litImp' :: Lit' s -> Lit' s -> Prop s
litImp' p q = lit' (neg p) \/ lit' q

litIff' :: Lit' s -> Lit' s -> Prop s
litIff' p q = litImp' p q /\ litImp' q p

varPred :: LitBundle s -> (Int -> Bool) -> Prop s
varPred x cond = andProp $ notInRangeClause <$> excludedRanges
  where
    allLo = _bundleLo x
    allHi = _bundleHi x
    excludedRanges = IS.toIntervals . IS.fromList $ [ i | i <- [allLo .. allHi - 1], not (cond i) ]
    notInRangeClause (lo, hi) = litImp' (lessThan' x hi) (lessThan' x lo)

-- (x <= y)
--  :<-> ∀(k. lo <= k <= hi). (y < k) --> (x < k)
--            ^^^^^^^^^^^^^ Note that it uses inclusive range!
varvarLe :: LitBundle s -> LitBundle s -> Prop s
varvarLe x y
  | xHi <= yLo = true
  | yHi <= xLo = false
  | otherwise = andProp $ level <$> [lo .. hi]
  where
    Bundle xLo xHi _ = x
    Bundle yLo yHi _ = y
    lo = max xLo yLo
    hi = min xHi yHi
    level k = litImp' (lessThan' y k) (lessThan' x k)

-- (x == y)
--  :<-> (lo <= x < hi)
--         /\ (lo <= y < hi)
--         /\ ∀(k. lo < k < hi). (x < k) <-> (y < k)
--                 ^^^^^^^^^^^ Note that it uses both-exclusive range
varvarEq :: LitBundle s -> LitBundle s -> Prop s
varvarEq x y = xInRange /\ yInRange /\ andProp (level <$> [lo + 1 .. hi - 1])
  where
    Bundle xLo xHi _ = x
    Bundle yLo yHi _ = y
    lo = max xLo yLo
    hi = min xHi yHi

    xInRange = geqThan x lo /\ lessThan x hi
    yInRange = geqThan y lo /\ lessThan y hi
    level k = litIff' (lessThan' x k) (lessThan' y k)

funVarEq :: (Int -> Int) -> LitBundle s -> LitBundle s -> Prop s
funVarEq f x y = andProp levelProps
  where
    Bundle yLo yHi _ = y
    levelProps = levelProp <$> [yLo .. yHi]

    -- levelProp k = lessThan y k <-> varPred x (\xVal -> f xVal < k)
    levelProp k =
         (lessThan y k \/ varPred x (\xVal -> f xVal >= k))
      /\ (geqThan y k  \/ varPred x (\xVal -> f xVal <  k))

dependent :: LitBundle s -> (Int -> Prop s) -> Prop s
dependent x cont = andProp (branches <$> [lo .. hi - 1])
  where
    Bundle lo hi _ = x
    -- branches k = varEq x k --> cont k
    branches k = varNe x k \/ cont k

----

findOneSolution :: (Ord v, Show v, HasCallStack) => Env v s -> Set v -> SAT s (Map v Int)
findOneSolution env visibleVars = do
  let model = Compose $ Map.fromSet (getBundle env) visibleVars
  assignments <- SAT.solve model
  return (bundleToInt <$> getCompose assignments)

excludeSolution :: (Ord v, Show v) => Env v s -> Map v Int -> SAT s ()
excludeSolution env solution = addClause' excludeClause
  where
    excludeClause = Map.toList solution >>= excludeOne
    excludeOne (var, k) =
      let x = getBundle env var
      in  [lessThan' x k, neg (lessThan' x (k + 1))]
