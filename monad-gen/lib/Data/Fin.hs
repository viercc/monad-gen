{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Fin where

import Text.Read (Read(readPrec), pfail)

import Data.Finite
import Data.Finitary.Enum qualified as Fin
import GHC.TypeNats (Nat, KnownNat, natVal)
import Data.Proxy ( Proxy(..) )

newtype Fin (n :: Nat) = Fin (Finite n)
  deriving stock (Eq, Ord)
  deriving newtype (Fin.Enum)

instance KnownNat n => Num (Fin n) where
  fromInteger = Fin . fromInteger
  (+) = error "I need only the literals"
  (*) = error "I need only the literals"
  abs = error "I need only the literals"
  signum = error "I need only the literals"
  (-) = error "I need only the literals"

instance KnownNat n => Show (Fin n) where
  show (Fin x) = show (toInteger x)

instance KnownNat n => Read (Fin n) where
  readPrec = readPrec >>= \x ->
    if 0 <= x && x < nVal
      then pure (fromIntegral x)
      else pfail
    where
      nVal = natVal (Proxy :: Proxy n)
