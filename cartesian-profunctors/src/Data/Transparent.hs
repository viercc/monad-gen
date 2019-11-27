{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Transparent(
  Transparent(..),
  eqDefault,
  compareDefault,
  enumList,
  enum,
  search
) where

import Data.Coerce

import Data.Void

import Control.Applicative
import Data.Functor.Contravariant
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker

import Data.Profunctor
import Data.Profunctor.Cartesian

import Data.List (foldl')
import Data.Word
import Data.Int
import Data.Bits
import Data.Char(chr, ord)

import Internal.AuxProfunctors

class (Eq x, Ord x) => Transparent x where
  describe :: (Cartesian p, Cocartesian p)
           => p x x

eqDefault :: forall x. Transparent x => x -> x -> Bool
eqDefault = coerce $ describe @x @EquivalenceP

compareDefault :: forall x. Transparent x => x -> x -> Ordering
compareDefault = coerce $ describe @x @ComparisonP

enumList :: forall x. (Transparent x) => [x]
enumList = coerce $ describe @x @(Joker [])

enum :: (Transparent x, Alternative f) => f x
enum = lowerCoYoJoker describe

search :: Transparent x => (x -> Bool) -> Maybe x
search cond = case describe of
  Absurd _  -> Nothing
  Exhaust p -> let x = p cond
               in if cond x then Just x else Nothing

data Exhaust a b = Absurd (a -> Void)
                 | Exhaust ((b -> Bool) -> b)

instance Profunctor Exhaust where
  lmap l (Absurd f)  = Absurd (f . l)
  lmap _ (Exhaust g) = Exhaust g
  
  rmap _ (Absurd f)  = Absurd f
  rmap r (Exhaust s) = Exhaust $ \cond -> r $ s (cond . r)

instance Cartesian Exhaust where
  proUnit = Exhaust (\_ -> ())
  Absurd p  *** _         = Absurd (\(a,_) -> p a)
  Exhaust _ *** Absurd q  = Absurd (\(_,a') -> q a')
  Exhaust p *** Exhaust q = Exhaust pq
    where
      pq cond =
        let subQuery b = q $ \b' -> cond (b, b')
            bGot = p $ \b -> cond (b, subQuery b)
        in (bGot, subQuery bGot)

instance Cocartesian Exhaust where
  proEmpty = Absurd id
  Absurd p  +++ Absurd q  = Absurd $ either p q
  Absurd _  +++ Exhaust q = Exhaust $ \cond -> Right $ q (cond . Right)
  Exhaust p +++ Absurd _  = Exhaust $ \cond -> Left $ p (cond . Left)
  Exhaust p +++ Exhaust q = Exhaust $ \cond ->
    let x = Left $ p (cond . Left)
        y = Right $ q (cond . Right)
    in if cond x then x else y

instance Transparent Void where
  describe = proEmpty

instance Transparent () where
  describe = proUnit

instance (Transparent x, Transparent y) => Transparent (Either x y) where
  describe = describe +++ describe

instance (Transparent x, Transparent y) => Transparent (x,y) where
  describe = describe *** describe

instance (Transparent x1, Transparent x2, Transparent x3)
         => Transparent (x1,x2,x3) where
  describe = dimap l r $ describe *** describe
    where
      l (x1,x2,x3) = (x1,(x2,x3))
      r (x1,(x2,x3)) = (x1,x2,x3)

instance (Transparent x1, Transparent x2, Transparent x3, Transparent x4)
         => Transparent (x1,x2,x3,x4) where
  describe = dimap l r $ describe *** describe
    where
      l (x1,x2,x3,x4) = (x1,(x2,x3,x4))
      r (x1,(x2,x3,x4)) = (x1,x2,x3,x4)

instance Transparent Bool where
  describe = dimap l r $ proUnit +++ proUnit
    where
      l False = Left ()
      l True  = Right ()
      r (Left _)  = False
      r (Right _) = True

instance Transparent Ordering where
  describe = dimap l r $ proUnit +++ (proUnit +++ proUnit)
    where
      l LT = Left ()
      l EQ = Right (Left ())
      l GT = Right (Right ())
      
      r (Left _) = LT
      r (Right (Left _)) = EQ
      r (Right (Right _)) = GT

instance Transparent x => Transparent (Maybe x) where
  describe = dimap l r $ proUnit +++ describe
    where
      l = maybe (Left ()) Right
      r = either (const Nothing) Just

instance Transparent x => Transparent [x] where
  describe = go 
    where
      go = dimap l r $ proUnit +++ (describe *** go)
      
      l [] = Left ()
      l (x:xs) = Right (x,xs)

      r (Left _) = []
      r (Right (x,xs)) = x:xs

instance Transparent Word8 where
  describe = b8
    where
      b1 = dBit
      b2 = b1 *** b1
      b4 = b2 *** b2
      b8 = dimap l8 r8 $ b4 *** b4
      
      l2 x = (x `shiftR` 1, x .&. 0x1)
      l4 x = (l2 (x `shiftR` 2), l2 (x .&. 0x3))
      l8 x = (l4 (x `shiftR` 4), l4 (x .&. 0xF))
      
      r2 (a,b) = a `shiftL` 1 .|. b
      r4 (a,b) = r2 a `shiftL` 2 .|. r2 b
      r8 (a,b) = r4 a `shiftL` 4 .|. r4 b

instance Transparent Int8 where
  describe = dimap fromIntegral fromIntegral (describe @Word8)

instance Transparent Word16 where
  describe = dimap l r $ describe @Word8 *** describe @Word8
    where
      l x = (fromIntegral (x `shiftR` 8), fromIntegral x)
      r (a,b) = fromIntegral a `shiftL` 8 .|. fromIntegral b

instance Transparent Int16 where
  describe = dimap fromIntegral fromIntegral $ describe @Word16

instance Transparent Word32 where
  describe = dimap l r $ describe @Word16 *** describe @Word16
    where
      l x = (fromIntegral (x `shiftR` 16), fromIntegral x)
      r (a,b) = fromIntegral a `shiftL` 16 .|. fromIntegral b

instance Transparent Int32 where
  describe = dimap fromIntegral fromIntegral $ describe @Word32

instance Transparent Word64 where
  describe = dimap l r $ describe @Word32 *** describe @Word32
    where
      l x = (fromIntegral (x `shiftR` 32), fromIntegral x)
      r (a,b) = fromIntegral a `shiftL` 32 .|. fromIntegral b

instance Transparent Int64 where
  describe = dimap fromIntegral fromIntegral $ describe @Word64

-- Irregular bitwidth types

instance Transparent Word where
  describe = dBits (finiteBitSize (0 :: Word))

instance Transparent Int where
  describe = dBits (finiteBitSize (0 :: Int))

instance Transparent Char where
  describe = dimap l r $ dBits 20 +++ dBits 16
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
dBit = dimap i2b b2i describe
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

----------------------------------------------

instance Transparent Integer where
  describe = dimap integerToRep repToInteger describeRep

data IntegerRep = Zeroes | Ones | C0 IntegerRep | C1 IntegerRep
  deriving (Show, Eq)

integerToRep :: Integer -> IntegerRep
integerToRep x
  | x >= 0    = loop Zeroes C0 C1 x
  | otherwise = loop Ones C1 C0 (complement x)
  where
    loop z c0 c1 = go
      where
        go n | n' == 0   = w32end loWord
             | otherwise = w32cons loWord (go n')
          where
            loWord = fromInteger n :: Word32
            n' = n `shiftR` 32

        cons b = if b then c1 else c0
        
        w32end 0 = z
        w32end n = cons (testBit n 0) (w32end (n `div` 2))
        
        w32cons n r = foldr (cons . testBit n) r [0..31]

repToInteger :: IntegerRep -> Integer
repToInteger = postproc . loop 0 0 []
  where
    mask :: Int -> Integer
    mask pos = negate (bit pos)
    
    loop :: Int -> Word32 -> [Integer] -> IntegerRep -> [Integer]
    loop 32 wordAcc allAcc r      = loop 0 0 (toInteger wordAcc : allAcc) r
    loop _  wordAcc allAcc Zeroes = toInteger wordAcc : allAcc
    loop i  wordAcc allAcc Ones   = (mask i .|. toInteger wordAcc) : allAcc
    loop i  wordAcc allAcc (C0 r) = loop (i+1) wordAcc allAcc r
    loop i  wordAcc allAcc (C1 r) = loop (i+1) (setBit wordAcc i) allAcc r

    postproc []     = error "Should never reach here"
    postproc (x:xs) = foldl' step x xs
      where step a y = (a `shiftL` 32) .|. y

describeRep :: (Cartesian p, Cocartesian p) => p IntegerRep IntegerRep
describeRep = dimap l r $ (proUnit +++ proUnit) +++ (go0 +++ go1)
  where
    l Zeroes = Left (Left ())
    l Ones   = Left (Right ())
    l (C0 n) = Right (Left n)
    l (C1 n) = Right (Right n)

    r = either (either (const Zeroes) (const Ones))
               (either C0 C1)
    
    go0 = dimap l0 r0 $ proUnit +++ (go0 +++ go1)
    l0 Zeroes = error "Invalid IntegerRep"
    l0 Ones = Left ()
    l0 (C0 n) = Right (Left n)
    l0 (C1 n) = Right (Right n)
    r0 = either (const Ones) (either C0 C1)

    go1 = dimap l1 r1 $ proUnit +++ (go0 +++ go1)
    l1 Zeroes = Left ()
    l1 Ones   = error "Invalid IntegerRep"
    l1 (C0 n) = Right (Left n)
    l1 (C1 n) = Right (Right n)
    r1 = either (const Zeroes) (either C0 C1)
