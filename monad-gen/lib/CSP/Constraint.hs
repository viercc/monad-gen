{-# LANGUAGE DeriveFunctor #-}

-- | Embedded DSL for Constraint-Satisfaction Problem
module CSP.Constraint where

import Data.Map.Strict (Map)
import Control.Monad ((>=>), ap)

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
conjunct = Conjunct

depend :: v -> ConstraintM v Int
depend x = Dependent x Pure

forAll :: [a] -> ConstraintM v a
forAll = Conjunct . fmap Pure
