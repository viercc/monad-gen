{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
module Data.Finitary.Enum(
  Enum(..),
  describeEnum,
  eqDefault,
  compareDefault,
  enumList,
  enum,
  coenum,
  cardinality,
  ptraverseFunction,
) where

import Data.Void

import Control.Applicative
import Data.Bifunctor.Clown

import Data.Profunctor.Cartesian

import Data.Word
import Data.Int

import Data.Functor.Contravariant.Divisible
import GHC.TypeNats (KnownNat (..), natVal)
import Data.Finite (Finite, shift, unshift, finites)
import Data.Finitary (Finitary(..))
import Prelude hiding (Enum)
import Data.Profunctor.FinFn
import Data.Functor.Contravariant (Contravariant(..))
import Data.Profunctor (Profunctor(..))

-- | @Enum x@ is @Finitary x@ but you can't get @Cardinality n@ at type level.
--
-- ==== Laws
-- 
-- The two functions @f :: x -> Finite n@ and @g :: Finite n -> x@
-- obtained by 'withEnum' must be isomorphism.
-- 
-- > withEnum body = body f g
-- > g . f = id :: x -> x
-- > f . g = id :: Finite n -> Finite n
-- 
-- Additionally, two methods 'enumeration' and 'withEnum' must be
-- equivalent to the ones defined in terms of the other.
--
-- > enumeration = withEnum makeFinFn
-- > withEnum body = withFinFn enumeration body
-- 
-- From these laws, @applyFinFn enumeration = id@ must follow.
class (Ord x) => Enum x where
  enumeration :: FinFn x x
  enumeration = withEnum makeFinFn

  withEnum :: (forall n. KnownNat n => (x -> Finite n) -> (Finite n -> x) -> r) -> r
  default withEnum :: Finitary x => (forall n. KnownNat n => (x -> Finite n) -> (Finite n -> x) -> r) -> r
  withEnum k = k toFinite fromFinite

eqDefault :: forall x. Enum x => x -> x -> Bool
eqDefault x1 x2 = withEnum (\toF _ -> toF x1 == toF x2)

compareDefault :: forall x. Enum x => x -> x -> Ordering
compareDefault x1 x2 = withEnum (\toF _ -> compare (toF x1) (toF x2))

enum :: (Enum x, Alternative f) => f x
enum = withEnum (\_ from -> asum (pure . from <$> finites))

coenum :: (Enum x, Decidable f, Divisible f) => f x
coenum = withEnum (\to _ -> contramap to $ runClown describeFinite)

cardinality :: forall x proxy. (Enum x) => proxy x -> Int
cardinality _ = withEnum @x getN
  where
    getN ::forall n. KnownNat n => (x -> Finite n) -> (Finite n -> x) -> Int
    getN _ _ = fromIntegral (natVal @n undefined)

enumList :: forall x. (Enum x) => [x]
enumList = withEnum (\_ from -> from <$> finites)

describeEnum :: (Enum x, Cartesian p, Cocartesian p) => p x x
describeEnum = withEnum $ \to from -> dimap to from describeFinite

ptraverseFunction :: forall x p a b. (Enum x, Cartesian p) => p a b -> p (x -> a) (x -> b)
ptraverseFunction p = withEnum @x $ \to from -> dimap (. from) (. to) (proPower p)

instance Enum Void
instance Enum ()
instance (Enum x, Enum y) => Enum (Either x y) where
  enumeration = enumeration +++ enumeration
  withEnum = withFinFn enumeration

instance (Enum x, Enum y) => Enum (x,y) where
  enumeration = enumeration *** enumeration
  withEnum = withFinFn enumeration

instance (Enum x1, Enum x2, Enum x3)=> Enum (x1,x2,x3) where
  enumeration = proProduct from to enumeration enumeration where
    from (x1,x2,x3) = (x1,(x2,x3))
    to (x1,(x2,x3)) = (x1,x2,x3)
  withEnum = withFinFn enumeration
instance (Enum x1, Enum x2, Enum x3, Enum x4) => Enum (x1,x2,x3,x4) where
  enumeration = proProduct from to enumeration enumeration where
    from (x1,x2,x3,x4) = ((x1,x2),(x3,x4))
    to ((x1,x2),(x3,x4)) = (x1,x2,x3,x4)
  withEnum = withFinFn enumeration
instance Enum Bool
instance Enum Ordering
instance Enum x => Enum (Maybe x) where
  withEnum k = withEnum @x (\from to -> k (maybe minBound (shift . from)) (fmap to . unshift))

instance Enum Word8
instance Enum Word16
instance Enum Word32
instance Enum Word64
instance Enum Word

instance Enum Int8
instance Enum Int16
instance Enum Int32
instance Enum Int64
instance Enum Int

instance Enum Char
