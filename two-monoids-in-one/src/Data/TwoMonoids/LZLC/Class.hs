module Data.TwoMonoids.LZLC.Class where

import Data.List.ZList
import Data.TwoMonoids.Class
import Data.TwoMonoids.LZ.Class

-- | 'TwoMonoids' with /left zero/ ('DMLZ') and
--   additional /left catch/ property: 'one' is right-absorbing element
--   for additive monoid.
--
-- @
-- -- left catch
-- one \<+\> x === one
-- @
class (DMLZ a) => DMLZLC a where
  {-# MINIMAL #-}

  -- | @msumZ@ is a @ZList@ algebra.
  --
  -- @
  -- msumZ . fmap msumZ === msumZ . 'Control.Monad.join'
  -- @
  --
  -- When you override the default implementation, it must keep the relation to
  -- the other methods:
  --
  -- @
  -- msumZ 'Nil' === 'zero'
  -- msumZ 'Zee' === 'one'
  -- msumZ (pure a) = msumZ ('Cons' a 'Nil') === a
  -- @
  msumZ :: ZList () a -> a
  msumZ = msum . go
    where
      go Nil = []
      go (Zee _) = [one]
      go (Cons a as) = a : go as

instance DMLZLC ()

instance (DMLZLC a, DMLZLC b) => DMLZLC (a, b)