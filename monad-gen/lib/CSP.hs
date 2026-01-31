{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveTraversable #-}
-- | Description of constraint solving problem
module CSP(
  -- * Problem definition
  VarName, VarRange(..),
  Variables,
  Constraint(..),

  -- * Solver entry point
  solveCSP,

  -- ** Correct-but-slow solver for debug
  solveCSPBruteForce,
  isValidAssignment,

  -- * Fine-grained solving API
  instantiateVars,
  compileConstraint,
  findOneSolution,
  runIterative
) where

import Control.Exception (assert)
import Data.Foldable (for_)
import GHC.Stack.Types (HasCallStack)
import Data.Map.Strict (Map)
import qualified Data.IntervalSet as IS

import Control.Monad.SAT
import qualified Data.Map.Strict as Map
import qualified Data.Vector.Strict as SV

import Data.IORef
import Control.Monad.IO.Class (liftIO)
import Data.Set (Set)
import Data.Functor.Compose (Compose(..))
import Control.Monad (guard)

-- * Type definitions

type VarName = String
data VarRange = VarRange
  !Int -- ^ lower bound (inclusive)
  !Int -- ^ upper bound (exclusive)

type Variables = Map VarName VarRange

data Constraint =
    Never
    -- ^ always false
  | Conjunct [Constraint]
    -- ^ conjunction (AND) of multiple constraints
    --   (Conjunct [] is "always satisfied")
  | VarImmEq VarName Int
    -- ^ x == k
  | VarImmNe VarName Int
    -- ^ x /= k
  | VarPred VarName (Int -> Bool)
    -- ^ p x
  | VarVarEq VarName VarName
    -- ^ x == y
  | VarVarNe VarName VarName
    -- ^ x /= y
  | VarVarLe VarName VarName
    -- ^ x <= y
  | FunVarEq (Int -> Int) VarName VarName
    -- ^ f x == y
  | Dependent VarName (Int -> Constraint)
    -- ^ Constraints depending on a value of a variable

solveCSP :: Variables -> [Constraint] -> Set VarName -> IO [Map VarName Int]
solveCSP vars constraints visibleVars = runIterative $ do
  env <- instantiateVars vars
  for_ constraints (addProp . compileConstraint env)
  pure (findOneSolution env visibleVars, excludeSolution env)

solveCSPBruteForce :: Variables -> [Constraint] -> Set VarName -> [Map VarName Int]
solveCSPBruteForce vars cons visibleVars = do
  assignment <- traverse (\(VarRange lo hi) -> [lo .. hi - 1]) vars
  guard $ all (isValidAssignment assignment) cons
  pure $ Map.restrictKeys assignment visibleVars

isValidAssignment :: Map VarName Int -> Constraint -> Bool
isValidAssignment env con = case con of
  Never -> False
  Conjunct cons -> all (isValidAssignment env) cons
  VarImmEq var k -> justTrue $ (k ==) <$> lup var
  VarImmNe var k -> justTrue $ (k /=) <$> lup var
  VarPred var cond -> justTrue $ cond <$> lup var
  VarVarEq varX varY -> justTrue $ (==) <$> lup varX <*> lup varY
  VarVarNe varX varY -> justTrue $ (/=) <$> lup varX <*> lup varY
  VarVarLe varX varY -> justTrue $ (<=) <$> lup varX <*> lup varY
  FunVarEq f varX varY -> justTrue $ (\x y -> f x == y) <$> lup varX <*> lup varY
  Dependent varX cont -> justTrue $ isValidAssignment env . cont <$> Map.lookup varX env
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

type Env s = Map VarName (LitBundle s)

type Clause' s = [Lit' s]

addClause' :: Clause' s -> SAT s ()
addClause' clause' = do
  conv <- noconstant
  addClause (conv <$> clause')

bundleToInt :: Bundle Bool -> Int
bundleToInt (Bundle lo _ vec) = lo + length (filter not $ SV.toList vec)

getBundle :: HasCallStack => Env s -> VarName -> LitBundle s
getBundle env name = Map.findWithDefault err name env
  where
    err = error $ "Variable not found: " ++ show name

lessThan' :: LitBundle s -> Int -> Lit' s
lessThan' (Bundle lo hi vec) k
  | k <= lo || hi <= lo = LitFalse
  | k >= hi = LitTrue
  | otherwise = LitHit $ vec SV.! (k - lo - 1)

lessThan :: LitBundle s -> Int -> Prop s
lessThan x k = lit' (lessThan' x k)

instantiateVars :: Variables -> SAT s (Env s)
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
  | n <= 0 = addClause [] >> pure (Bundle lo lo SV.empty)
             -- ^ Unsatisfiable
  | n == 1 = pure (Bundle lo hi SV.empty)
             -- ^ The variable is actually constant (x == lo): no literals needed
  | otherwise = assert (n > 1) $ do
      -- instantiate x_i for all (1 <= i < n)
      lits <- SV.replicateM (n - 1) newLit
      -- (x_i → x_{i+1}) for all i defined
      for_ (SV.zip lits (SV.drop 1 lits)) $ \(xi, xi') ->
        addClause [neg xi, xi']
      pure (Bundle lo hi lits)
  where
    n = hi - lo

------------------

-- | Translate 'Constraint' to 'Prop'.
compileConstraint :: HasCallStack => Env s -> Constraint -> Prop s
compileConstraint env con  = case con of
  Never -> false
  Conjunct cons -> andProp (compileConstraint env <$> cons)
  VarImmEq varName k -> varEq (getBundle env varName) k
  VarImmNe varName k -> varNe (getBundle env varName) k
  VarPred varName cond -> varPred (getBundle env varName) cond
  VarVarEq varX varY -> varvarEq (getBundle env varX) (getBundle env varY)
  VarVarNe varX varY -> dependent (getBundle env varX) (varNe (getBundle env varY))
  VarVarLe varX varY -> varvarLe (getBundle env varX) (getBundle env varY)
  FunVarEq f varX varY -> funVarEq f (getBundle env varX) (getBundle env varY)
  Dependent varName subCon -> dependent (getBundle env varName) (compileConstraint env . subCon)

varEq :: LitBundle s -> Int -> Prop s
varEq x k = neg (lessThan x k) /\ lessThan x (k + 1)

varNe :: LitBundle s -> Int -> Prop s
varNe x k = lessThan x k \/ neg (lessThan x (k + 1))

varPred :: LitBundle s -> (Int -> Bool) -> Prop s
varPred x cond = andProp $ notInRangeClause <$> excludedRanges
  where
    allLo = _bundleLo x
    allHi = _bundleHi x
    excludedRanges = IS.toIntervals . IS.fromList $ [ i | i <- [allLo .. allHi - 1], not (cond i) ]
    notInRangeClause (lo, hi) = lessThan x lo \/ neg (lessThan x hi)

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

    level k = lessThan y k --> lessThan x k


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

    xInRange = neg (lessThan x lo) /\ lessThan x hi
    yInRange = neg (lessThan y lo) /\ lessThan y hi
    level k = lessThan x k <-> lessThan y k

funVarEq :: (Int -> Int) -> LitBundle s -> LitBundle s -> Prop s
funVarEq f x y = andProp levelProps
  where
    Bundle yLo yHi _ = y
    levelProps = levelProp <$> [yLo .. yHi]

    levelProp k = varPred x (\xVal -> f xVal < k) <-> lessThan y k

dependent :: LitBundle s -> (Int -> Prop s) -> Prop s
dependent x cont = andProp (branches <$> [lo .. hi - 1])
  where
    Bundle lo hi _ = x
    branches k = varEq x k --> cont k

-- * SAT utility

-- | Literal or constant
data Lit' s = LitFalse | LitHit (Lit s) | LitTrue

instance Neg (Lit' s) where
  neg LitFalse = LitTrue
  neg (LitHit l) = LitHit (neg l)
  neg LitTrue = LitFalse

lit' :: Lit' s -> Prop s
lit' l' = case l' of
  LitFalse -> false
  LitHit l -> lit l
  LitTrue -> true

noconstant :: SAT s (Lit' s -> Lit s)
noconstant = do
  t <- trueLit
  pure $ \l' -> case l' of
    LitFalse -> neg t
    LitHit l -> l
    LitTrue -> t

andProp :: [Prop s] -> Prop s
andProp = foldr (/\) true

----

findOneSolution :: Env s -> Set VarName -> SAT s (Map VarName Int)
findOneSolution env visibleVars = do
  let model = Compose $ Map.fromSet (getBundle env) visibleVars
  assignments <- solve model
  return (bundleToInt <$> getCompose assignments)

excludeSolution :: Env s -> Map VarName Int -> SAT s ()
excludeSolution env solution = addClause' excludeClause
  where
    excludeClause = Map.toList solution >>= excludeOne
    excludeOne (var, k) =
      let x = getBundle env var
      in  [lessThan' x k, neg (lessThan' x (k + 1))]

runIterative :: forall a. (forall s. SAT s (SAT s a, a -> SAT s ())) -> IO [a]
runIterative generator =
  do results <- newIORef []
     let body :: forall s'. SAT s' ()
         body = do
           (nextSolution, exclude) <- generator
           let loop = do
                a <- nextSolution
                liftIO $ modifyIORef' results (a:)
                exclude a
                loop
           loop
     _ <- runSATMaybe body
     readIORef results