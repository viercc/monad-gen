{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
module Data.Transparent(
  Transparent(..),
  describe,
  eqDefault,
  compareDefault,
  enumList,
  enum,
  coenum,
  cardinality,
  search,
) where

import Data.Coerce
import Data.Void

import Control.Applicative
import Data.Functor.Contravariant
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker

import Data.Profunctor
import Data.Profunctor.Cartesian
import Data.Profunctor.Exhaust

import Data.Word
import Data.Int
import Data.Bits
import Data.Char(chr, ord)

import Data.Profunctor.Extra
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Counting (Counting(..))

class (Ord x) => Transparent x where
  describeOn :: forall p a b. (Cartesian p, Cocartesian p)
               => (a -> x) -> (x -> b) -> p a b

describe :: forall x p. (Transparent x, Cartesian p, Cocartesian p) => p x x
describe = describeOn id id

eqDefault :: forall x. Transparent x => x -> x -> Bool
eqDefault = coerce $ describe @x @EquivalenceP

compareDefault :: forall x. Transparent x => x -> x -> Ordering
compareDefault = coerce $ describe @x @ComparisonP

enum :: (Transparent x, Alternative f) => f x
enum = runJoker describe

coenum :: (Transparent x, Decidable f, Divisible f) => f x
coenum = runClown describe

cardinality :: forall x proxy. (Transparent x) => proxy x -> Int
cardinality _ = getCounting (describe @x)

enumList :: forall x. (Transparent x) => [x]
enumList = coerce $ describe @x @(Joker [])

search :: Transparent x => (x -> Bool) -> Maybe x
search cond = case describe of
  Absurd _  -> Nothing
  Exhaust p -> let x = p cond
               in if cond x then Just x else Nothing

instance Transparent Void where
  describeOn f _ = lmap f proEmpty

instance Transparent () where
  describeOn _ g = rmap g proUnit

instance (Transparent x, Transparent y) => Transparent (Either x y) where
  describeOn f g = dimap f g (describe +++ describe)

instance (Transparent x, Transparent y) => Transparent (x,y) where
  describeOn f g = dimap f g (describe *** describe)

instance (Transparent x1, Transparent x2, Transparent x3)
         => Transparent (x1,x2,x3) where
  describeOn f g = describeOn (l . f) (g . r)
    where
      l (x1,x2,x3) = (x1,(x2,x3))
      r (x1,(x2,x3)) = (x1,x2,x3)

instance (Transparent x1, Transparent x2, Transparent x3, Transparent x4)
         => Transparent (x1,x2,x3,x4) where
  describeOn f g = describeOn (l . f) (g . r)
    where
      l (x1,x2,x3,x4) = ((x1,x2),(x3,x4))
      r ((x1,x2),(x3,x4)) = (x1,x2,x3,x4)

instance Transparent Bool where
  describeOn f g = describeOn (l . f) (g . r)
    where
      l False = Left ()
      l True  = Right ()
      r (Left _)  = False
      r (Right _) = True

instance Transparent Ordering where
  describeOn f g = describeOn (l . f) (g . r)
    where
      l LT = Left ()
      l EQ = Right (Left ())
      l GT = Right (Right ())
      
      r (Left _) = LT
      r (Right (Left _)) = EQ
      r (Right (Right _)) = GT

instance Transparent x => Transparent (Maybe x) where
  describeOn f g = describeOn (l . f) (g . r)
    where
      l = maybe (Left ()) Right
      r = either (const Nothing) Just

newtype DescribeFiniteBits a = DescribeFiniteBits a
   deriving newtype (Eq, Ord, Bits, FiniteBits)

instance (Ord a, FiniteBits a) => Transparent (DescribeFiniteBits a) where
  describeOn f g = dimap f g dFiniteBits

deriving via (DescribeFiniteBits Word8) instance Transparent Word8
deriving via (DescribeFiniteBits Word16) instance Transparent Word16
deriving via (DescribeFiniteBits Word32) instance Transparent Word32
deriving via (DescribeFiniteBits Word64) instance Transparent Word64
deriving via (DescribeFiniteBits Word) instance Transparent Word

deriving via (DescribeFiniteBits Int8) instance Transparent Int8
deriving via (DescribeFiniteBits Int16) instance Transparent Int16
deriving via (DescribeFiniteBits Int32) instance Transparent Int32
deriving via (DescribeFiniteBits Int64) instance Transparent Int64
deriving via (DescribeFiniteBits Int) instance Transparent Int

instance Transparent Char where
  describeOn f g = dimap (l . f) (g . r) $ dBits 20 +++ dBits 16
    where
      -- Unicode code points are in range: 0x000000 <= x <= 0x10FFFF
      -- Char ~ 2^20 + 2^16
      --        ^^^^   ^^^^ 0x100000 <= x <= 0x10FFFF
      --        |||| 0x000000 <= x <= 0x0FFFFF
      
      thresh = 0x100000
      
      l c = let x = ord c
            in if x < 0x100000 then Left x else Right (x - thresh)
      r = chr . either id (thresh +)

dBit :: (Bits a, Cartesian p, Cocartesian p) => p a a
dBit = describeOn i2b b2i
  where
    i2b x = testBit x 0
    b2i False = zeroBits
    b2i True  = bit 0

dBits :: (Bits a, Cartesian p, Cocartesian p) => Int -> p a a
dBits n
  | n <= 0 = error "bad!"
  | n == 1 = dBit
  | otherwise =
      case separate n of
        (0, p) -> dBitsPow2 p
        (m, p) ->
          let l x = (x `shiftR` p, x)
              r (a,b) = a `shiftL` p .|. b
          in dimap l r $ dBits m *** dBitsPow2 p

dFiniteBits :: forall a p. (FiniteBits a, Cartesian p, Cocartesian p) => p a a
dFiniteBits = dBits (finiteBitSize (zeroBits :: a))

separate :: Int -> (Int, Int)
-- must be x > 1
separate x = (r, bit p)
  where
    p = finiteBitSize (0 :: Int) - countLeadingZeros x - 1
    r = clearBit x p

dBitsPow2 :: (Bits a, Cartesian p, Cocartesian p) => Int -> p a a
dBitsPow2 1 = dBit
dBitsPow2 n =
  let m = n `div` 2
      halfBits = dBitsPow2 m
      l x = (x `shift` (-m), x)
      r (a,b) = a `shift` m .|. b
  in dimap l r $ halfBits *** halfBits

