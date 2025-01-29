{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
module Data.Torsor(
  Torsor(..),
  (<---),

  GroupToTorsor(..),
  TorsorToGroup(..),
) where

import Data.Monoid (Dual (..), Sum)
import Data.Group
import Data.Default
import Data.Void

-- | A torsor (also known as heap) is an algebraic structure which is almost 'Group'.
--   
-- ===== What is Torsor
--  
-- @Torsor x@ is defined by just one operation 'paral' with three arguments,
-- satisfying the following equations (Torsor laws):
--   
-- @
-- -- Cancellation
-- paral a a b === b === paral b c c
-- -- Associativity
-- paral a b (paral c d e) === paral (paral a b c) d e
-- @
--   
-- For any @Group g@, the following @paral@ defines a torsor.
--   
-- @
-- 'paral' a b c = a '<>' 'invert' b <> c
-- @
--
-- Conversely, *any* @Torsor x@ with at least one element
-- @def :: x@ can be seen as a @Group x@.
--   
-- @
-- x <> y = paral x def y
-- mempty = def
-- invert x = paral def x def
-- @
--   
-- The Torsor-to-Group conversion can be reversed by the first Group-to-Torsor conversion,
-- and the Group-to-Torsor conversion can be reversed if one \"remembers\"
-- the identity of the group @mempty@.
-- In this sense, a @Torsor@ can be thought of as a @Group@ but forgot which
-- element was the idenitity.
-- 
-- ===== About the name @Torsor@ and @paral@
-- 
-- Usually, the name "torsor" is given to **non-empty** sets equipped with
-- @paral@ function. Contrary to the custom, this class allows an empty type
-- to have an instance. If we want to be precise, this class should be named
-- `Pseudotorsor`.
-- 
-- The name of the ternary operation @paral@ is short for \"parallelogram\",
-- representing the common case of a torsor being the set of points in a plane.
-- 
-- A set of points (@A,B,C,...@) in a plane can be seen as a torsor by taking
-- the unique parallelogram @ABCD@ determined by three points @A,B,C@ as
-- the definition of @paral A B C = D@.
-- 
-- >     A----D = paral A B C
-- >    /    /
-- >   /    /
-- >  B----C
-- 
-- If the plane has the designated origin, each point can be
-- represented by the vector from the origin, and @paral@
-- can be written simply @paral A B C = A - B + C@ using addition and subtraction
-- of vectors.
class Torsor x where
  paral :: x -> x -> x -> x

instance Torsor Void where
  paral = absurd

instance Torsor () where
  paral _ _ _ = ()

instance Torsor Bool where
  paral a b c = a `xor` b `xor` c
    where
      xor = (/=)

instance (Torsor x, Torsor y) => Torsor (x,y) where
  paral (a,a') (b,b') (c,c') = (paral a b c, paral a' b' c')

instance (Torsor x) => Torsor (Dual x) where
  paral (Dual a) (Dual b) (Dual c) = Dual $ paral c b a

deriving via (GroupToTorsor (Sum a))
  instance Num a => Torsor (Sum a)

-- | An infix operator version of 'paral'.
--
-- @
-- (a <--- b) c = paral a b c
-- @
-- 
-- The cancellation law of torsor is written in terms of @(<---)@:
--
-- @
-- (a <--- a)   === id
-- (a <--- b) b === a
-- @
--
-- Also, the laws imply:
-- 
-- @
-- (a <--- b) . (b <--- c) === (a <--- c)
-- ((a <--- b) c) <--- c) === (a <--- b)
-- @
(<---) :: Torsor x => x -> x -> x -> x
(<---) = paral

infix 6 <---

newtype GroupToTorsor g = ToTorsor { asGroup :: g }
  deriving stock (Show, Read)
  deriving newtype (Eq, Ord, Semigroup, Monoid, Group, Default)

instance Group g => Torsor (GroupToTorsor g) where
  paral a b c = a <> invert b <> c

newtype TorsorToGroup x = ToGroup { asTorsor :: x }
  deriving stock (Show, Read)
  deriving newtype (Eq, Ord, Torsor, Default)

instance (Default x, Torsor x) => Semigroup (TorsorToGroup x) where
  a <> b = paral a def b

instance (Default x, Torsor x) => Monoid (TorsorToGroup x) where
  mempty = def

instance (Default x, Torsor x) => Group (TorsorToGroup x) where
  invert a = paral def a def
