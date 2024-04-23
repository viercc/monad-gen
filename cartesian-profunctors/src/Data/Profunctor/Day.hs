{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
module Data.Profunctor.Day(
  Day(..)
) where

import Data.Profunctor (Profunctor (..))
import Data.Profunctor.Monad (ProfunctorFunctor (..))

data Day t p q a b where
  Day :: p a1 b1 -> q a2 b2 -> (a -> t a1 a2) -> (t b1 b2 -> b) -> Day t p q a b

deriving instance Functor (Day t p q a)

instance Profunctor (Day t p q) where
    dimap f g (Day p q opA opB) = Day p q (opA . f) (g . opB)

instance ProfunctorFunctor (Day t p) where
    promap qr (Day p q opA opB) = Day p (qr q) opA opB
