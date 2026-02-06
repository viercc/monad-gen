{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}

-- | Embedded DSL for Constraint-Satisfaction Problem
module CSP.Constraint(
  VarRange(..),
  Variables,

  ConstraintAtom(..),
  ConstraintM(..),
  Constraint,

  never, always, ensure,
  conjunct, depend, forAll,

  (%<.), (%==.), (%/=.), satisfy,
  (%==%), (%/=%), (%<=%),
  functionEq,

  -- * assignment
  isValidAssignment,
  isValidAssignmentAtom,
  assume

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as MapMerge
import Control.Monad ((>=>), ap)
import Data.Bifunctor (Bifunctor(..))
import qualified Data.List as List

-- * Type definitions

data VarRange = VarRange
  !Int -- ^ lower bound (inclusive)
  !Int -- ^ upper bound (exclusive)
  deriving (Show)

type Variables v = Map v VarRange

data ConstraintAtom v =
    VarImmLt v Int
    -- ^ x < k
  | VarImmEq v Int
    -- ^ x == k
  | VarImmNe v Int
    -- ^ x /= k
  | VarPred v (Int -> Bool)
    -- ^ p x
  | VarVarEq v v
    -- ^ x == y
  | VarVarNe v v
    -- ^ x /= y
  | VarVarLe v v
    -- ^ x <= y
  | FunVarEq (Int -> Int) v v
    -- ^ f x == y

data ConstraintM v a =
    Pure a
  | Never
    -- ^ always false
  | Conjunct [ConstraintM v a]
    -- ^ conjunction (AND) of multiple constraints
    --   (Conjunct [] is "always satisfied")
  | Dependent v (Int -> ConstraintM v a)
    -- ^ Constraints depending on a value of a variable
  deriving Functor

instance Applicative (ConstraintM v) where
  pure = Pure
  (<*>) = ap

instance Monad (ConstraintM v) where
  Pure a >>= f = f a
  Never >>= _ = Never
  Conjunct mas >>= f = Conjunct (fmap (>>= f) mas)
  Dependent x cont >>= f = Dependent x (cont >=> f)

type Constraint v = ConstraintM v (ConstraintAtom v)

-- | Evaluates false regardless of subsequent expression
never :: ConstraintM v a
never = Never

-- | Evaluates true regardless of subsequent expression
always :: ConstraintM v a
always = Conjunct []

ensure :: Bool -> ConstraintM v ()
ensure False = never
ensure True  = pure ()

infix 3 %<.
infix 3 %==.
infix 3 %/=.
infix 3 %==%
infix 3 %/=%
infix 3 %<=%

(%<.) :: v -> Int -> Constraint v
x %<. k = Pure $ VarImmLt x k

(%==.) :: v -> Int -> Constraint v
x %==. k = Pure $ VarImmEq x k

(%/=.) :: v -> Int -> Constraint v
x %/=. k = Pure $ VarImmNe x k

satisfy :: v -> (Int -> Bool) -> Constraint v
satisfy x cond = Pure $ VarPred x cond

(%==%) :: v -> v -> Constraint v
x %==% y = Pure $ VarVarEq x y

(%/=%) :: v -> v -> Constraint v
x %/=% y = Pure $ VarVarNe x y

(%<=%) :: v -> v -> Constraint v
x %<=% y = Pure $ VarVarLe x y

functionEq :: (Int -> Int) -> v -> v -> Constraint v
functionEq f x y = Pure $ FunVarEq f x y

conjunct :: [Constraint v] -> Constraint v
conjunct = Conjunct . foldr op []
  where
    op Never _ = [Never]
    op (Conjunct cs) r = cs ++ r
    op c r = c : r

depend :: v -> ConstraintM v Int
depend x = Dependent x Pure

forAll :: [a] -> ConstraintM v a
forAll = Conjunct . fmap Pure

-- * Evaluate for assignment

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

assume :: Ord v => Map v Int -> (Variables v, Constraint v) -> (Variables v, Constraint v)
assume givens (vars, con) = case assumeVarDefs givens vars of
  Nothing -> (vars, never)
  Just vars' -> simplifyConstraint vars' con

assumeVarDefs :: Ord v => Map v Int -> Variables v -> Maybe (Variables v)
assumeVarDefs =
  MapMerge.mergeA
    -- If "givens" contain definitions missing in "vars", make constant range
    (MapMerge.traverseMissing (\_ i -> Just (VarRange i (i + 1))))
    -- Keep variables not appeared "givens" intact
    MapMerge.preserveMissing
    -- Use the following f to update matched case
    (MapMerge.zipWithAMatched f)
  where
    f _ i (VarRange lo hi)
     | lo <= i && i < hi = Just $ VarRange i (i + 1)
     | otherwise         = Nothing

(!) :: Ord v => Variables v -> v -> VarRange
vars ! x = Map.findWithDefault err x vars
  where
    err = error "undefined variable"

simplifyConstraint :: 
     Ord v
  => Variables v -> Constraint v -> (Variables v, Constraint v)
simplifyConstraint vars con = case con of
  Pure s -> simplifyConstraintAtom vars s
  Never -> (vars, Never)
  Conjunct cs -> second conjunct $ List.mapAccumL simplifyConstraint vars cs
  Dependent var cont -> case vars ! var of
    VarRange lo hi
      | lo + 1 == hi -> simplifyConstraint vars (cont lo)
      | otherwise    -> (vars, con)

simplifyConstraintAtom :: Ord v => Variables v -> ConstraintAtom v -> (Variables v, Constraint v)
simplifyConstraintAtom vars con = case con of
  VarImmLt var k -> varLt vars var k
  VarImmEq var k -> varEq vars var k
  VarImmNe var k -> varNe vars var k
  VarPred var cond -> varPred vars var cond
  VarVarEq varX varY -> varvarEq vars varX varY
  VarVarNe varX varY -> varvarNe vars varX varY
  VarVarLe varX varY -> varvarLe vars varX varY
  FunVarEq f varX varY -> funVarEq vars f varX varY

-- headOr a0 as = head (as ++ [a0])
headOr :: a -> [a] -> a
headOr a0 [] = a0
headOr _  (a0:_) = a0

{-

>>> filterRange (const False) (VarRange 0 4)
Nothing
>>> filterRange (const True) (VarRange 0 4)
Just (VarRange 0 4)
>>> filterRange even (VarRange 0 3)
Just (VarRange 0 3)
>>> filterRange even (VarRange 0 2)
Just (VarRange 0 1)
>>> filterRange odd (VarRange 0 2)
Just (VarRange 1 2)

-}
filterRange :: (Int -> Bool) -> VarRange -> Maybe VarRange
filterRange cond (VarRange lo hi)
  | lo' == hi = Nothing
  | otherwise = Just (VarRange lo' (hi' + 1))
  where
    -- lo' = least value where `cond` is True,
    -- or lo' == hi indicating no value was True
    lo' = headOr hi $ dropWhile (not . cond) [lo .. hi - 1]
    -- hi' = largest value where `cond` is True
    hi' = headOr lo' $ dropWhile (not . cond) [hi - 1, hi - 2 .. lo' + 1]

varEq, varGe, varLt, varNe :: Ord v => Variables v -> v -> Int -> (Variables v, Constraint v)
varEq vars var k = case vars ! var of
  VarRange lo hi
    | lo <= k && k < hi -> let !vars' = Map.insert var (VarRange k (k+1)) vars in (vars', always)
    | otherwise -> (vars, never)
varGe vars var k = case vars ! var of
  VarRange lo hi
    | k <= lo -> (vars, always)
    | lo < k && k < hi -> let !vars' = Map.insert var (VarRange k hi) vars in (vars', always)
    | otherwise -> (vars, never)
varLt vars var k = case vars ! var of
  VarRange lo hi
    | k <= lo -> (vars, never)
    | lo < k && k < hi -> let !vars' = Map.insert var (VarRange lo k) vars in (vars', always)
    | otherwise -> (vars, always)
varNe vars var k = case vars ! var of
  VarRange lo hi
    | k < lo || k >= hi -> (vars, always)
    | k == lo && k + 1 == hi -> (vars, never)
    | k == lo -> let !vars' = Map.insert var (VarRange (lo + 1) hi) vars in (vars', always)
    | k == hi - 1 -> let !vars' = Map.insert var (VarRange lo (hi - 1)) vars in (vars', always)
    | otherwise -> (vars, var %/=. k)

varPred :: Ord v => Variables v -> v -> (Int -> Bool) -> (Variables v, Constraint v)
varPred vars var cond = case filterRange cond (vars ! var) of
  Nothing -> (vars, never)
  Just r@(VarRange lo hi)
    | hi - lo <= 2 -> let !vars' = Map.insert var r vars in (vars', always)
    | otherwise    -> let !vars' = Map.insert var r vars in (vars', var `satisfy` cond)

lookupKnown :: Ord v => v -> Variables v -> Maybe Int
lookupKnown v vars = do
  VarRange lo hi <- Map.lookup v vars
  if lo + 1 == hi
    then Just lo
    else Nothing

varvarEq, varvarNe, varvarLe :: Ord v => Variables v -> v -> v -> (Variables v, Constraint v)
varvarEq vars varX varY 
  | lo >= hi     = (vars, never)
  | lo == hi - 1 = (vars', always)
  | otherwise    = (vars', varX %==% varY)
  where
    VarRange loX hiX = vars ! varX
    VarRange loY hiY = vars ! varY
    lo = max loX loY
    hi = min hiX hiY
    r = VarRange lo hi
    !vars' = Map.insert varX r $ Map.insert varY r vars

varvarNe vars varX varY = case (lookupKnown varX vars, lookupKnown varY vars) of
  (Just x, Just y)
    | x /= y    -> (vars, always)
    | otherwise -> (vars, never)
  (Just x, _) -> varNe vars varY x
  (_, Just y) -> varNe vars varX y
  _ -> (vars, varX %/=% varY)
varvarLe vars varX varY = case (lookupKnown varX vars, lookupKnown varY vars) of
  (Just x, Just y)
    | x <= y    -> (vars, always)
    | otherwise -> (vars, never)
  (Just x, _) -> varGe vars varY x
  (_, Just y) -> varLt vars varX (y - 1)
  _ -> (vars, varX %<=% varY)

funVarEq :: Ord v => Variables v -> (Int -> Int) -> v -> v -> (Variables v, Constraint v)
funVarEq vars f varX varY = case (lookupKnown varX vars, lookupKnown varY vars) of
  (Just x, Just y)
    | f x == y    -> (vars, always)
    | otherwise -> (vars, never)
  (Just x, _) -> varEq vars varY (f x)
  (_, Just y) -> varPred vars varX (\x -> f x == y)
  _ -> (vars, functionEq f varX varY)
