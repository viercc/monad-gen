{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
module ModelFinder.Term(
  -- * Term
  Term, L(..),
  con, fun, liftFun,

  -- * Property
  Property(..),
  Property'(..),
  runProperty
) where

import Data.Equality.Utils

-- | Functions and constants
data L f a r = Con a | Fun (f r)
  deriving (Functor, Foldable, Traversable, Show, Eq, Ord)

-- Note that the following constraint implication
-- hold.
--
-- > (Ord a, Language f) => Language (L f a)
-- 
-- Many functions from hegg library requiring (Language (L f a))
-- are used with the above (Ord a, Language f) constraint.

type Term f a = Fix (L f a)

con :: a -> Term f a
con = Fix . Con

fun :: f (Term f a) -> Term f a
fun = Fix . Fun

liftFun :: Functor f => f a -> Term f a
liftFun = fun . fmap con

data Property' f a
  = Equals (Term f a) (Term f a)
  | ForAll (a -> Property' f a)

newtype Property f = Property (forall a. Property' f a)

runProperty :: [a] -> Property f -> [(Term f a, Term f a)]
runProperty as (Property prop) = go prop
  where
    go (Equals t1 t2) = [(t1, t2)]
    go (ForAll prop') = as >>= go . prop'
