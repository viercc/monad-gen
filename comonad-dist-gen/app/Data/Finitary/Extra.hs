{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Finitary functions
module Data.Finitary.Extra(
  Fn(..),
  fnToVec, vecToFn,
  showFn,
  prettyPrintFn,
  prettyPrintFn2
) where

import Data.Foldable (Foldable(..))

import Data.Finitary
import Data.Finite ()
import Data.Vector.Sized (Vector)
import GHC.Exts (proxy#)
import GHC.TypeNats (natVal', type (^))
import qualified Data.Vector.Sized as V
import Data.List (intercalate)
import Data.Functor.Classes
import qualified Data.Map.Lazy as Map

newtype Fn a b = Fn { apply :: a -> b }
  deriving stock Functor
  deriving (Applicative, Monad) via ((->) a)

instance (Finitary a, Show a, Show b) => Show (Fn a b) where
  showsPrec p (Fn f) = showParen (p > 0) $ (("Fn " ++ showFn f) ++)

instance (Finitary a) => Foldable (Fn a) where
  length _ = fromInteger . toInteger $ natVal' @(Cardinality a) proxy#
  null _ = (== 0) $ natVal' @(Cardinality a) proxy#

  toList fn = apply fn <$> inhabitants
  foldMap g (Fn f) = foldMap (g . f) inhabitants
  foldr step z (Fn f) = foldr (\a r -> step (f a) r) z inhabitants
  foldl' step z (Fn f) = foldl' (\r a -> step r (f a)) z inhabitants

instance (Finitary a) => Traversable (Fn a) where
  traverse g fn = vecToFn <$> traverse g (fnToVec fn)

fnToVec :: (Finitary a) => Fn a b -> Vector (Cardinality a) b
fnToVec fn = V.generate (apply fn . fromFinite)
{-# INLINE [3] fnToVec #-}

vecToFn :: (Finitary a) => Vector (Cardinality a) b -> Fn a b
vecToFn v = Fn (V.index v . toFinite)
{-# INLINE [3] vecToFn #-}

{-# RULES "fnToVec_iso1" forall x. fnToVec (vecToFn x) = x #-}
{-# RULES "fnToVec_iso2" forall x. vecToFn (fnToVec x) = x #-}

instance (Finitary a, Eq b) => Eq (Fn a b) where
  (==) = eq1

instance (Finitary a) => Eq1 (Fn a) where
  liftEq eq fn1 fn2 = and (eq <$> fn1 <*> fn2)

instance (Finitary a, Ord b) => Ord (Fn a b) where
  compare = compare1

instance (Finitary a) => Ord1 (Fn a) where
  liftCompare cmp fn1 fn2 = fold (cmp <$> fn1 <*> fn2)

instance (Finitary a, Finitary b) => Finitary (Fn a b) where
  type Cardinality (Fn a b) = Cardinality b ^ Cardinality a

  fromFinite k = vecToFn (fromFinite k)
  toFinite fn = toFinite (fnToVec fn)

showFn :: (Finitary a, Show a, Show b) => (a -> b) -> String
showFn f = "\\case {" ++ intercalate ";" [ showCase a (f a) | a <- inhabitants ] ++ "}"
  where
    showCase a b = show a ++ " -> " ++ show b

prettyPrintFn :: (Finitary a, Show a, Show b) => String -> (a -> b) -> [String]
prettyPrintFn fnName fn =
  [ showsUnaryWith showsPrec fnName 0 a . equal . showsPrec 0 (fn a) $ "" | a <- inhabitants ]
  where
    equal = (" = " ++) 

prettyPrintFn2 :: (Finitary a, Show a, Finitary b, Show b, Finitary c, Show c) => String -> (a -> b -> c) -> [String]
prettyPrintFn2 fnName fn = usedFnDefs ++ fnBody
  where
    equal = (" = " ++)
    nameSubFn key = fnName ++ "_" ++ show key
    usedFn = [ (a, fa, toInteger (toFinite (Fn fa))) | a <- inhabitants, let fa = fn a ]
    fnBody = [ showsUnaryWith showsPrec fnName 0 a . equal . (nameSubFn key ++) $ "" | (a,_,key) <- usedFn ]

    usedFnMap = Map.fromList [ (key, fa) | (_, fa, key) <- usedFn ]
    usedFnDefs = do
      (key, fa) <- Map.toList usedFnMap
      prettyPrintFn (nameSubFn key) fa
