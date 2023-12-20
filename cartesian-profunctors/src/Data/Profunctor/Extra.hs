{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
module Data.Profunctor.Extra where

import Data.Functor.Contravariant
import Data.Bifunctor.Clown

type EquivalenceP = Clown Equivalence
type ComparisonP = Clown Comparison
