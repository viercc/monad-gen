module Data.Functor.Contravariant.Numbering where

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Void (absurd)

data Numbering a = No !Int (a -> Int)

instance Contravariant Numbering where
    contramap f (No n v) = No n (v . f)

instance Divisible Numbering where
    divide op (No nb f) (No nc g) = No (nb * nc) h
      where
        h a = 
            case op a of
                (b, c) -> f b * nc + g c
    
    conquer = No 1 (const 0)

instance Decidable Numbering where
  choose p (No nb f) (No nc g) = No (nb + nc) h
    where
      h a = case p a of
        Left b  -> f b
        Right c -> nb + g c
  lose f = No 0 (absurd . f)