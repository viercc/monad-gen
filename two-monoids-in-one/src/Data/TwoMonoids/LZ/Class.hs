module Data.TwoMonoids.LZ.Class where

import Data.List.ZList (ZList (..))
import Data.TwoMonoids.Class

-- | Double monoid with additional property (/left zero/):
--   'zero' is a right-absorbing element.
--
-- @
-- zero <> x = zero
-- @
class (TwoMonoids a) => DMLZ a where
  {-# MINIMAL #-}

  -- | @mprodZ@ is a @ZList ()@ algebra.
  --
  -- @
  -- mprodZ . fmap mprodZ === mprodZ . 'Control.Monad.join'
  -- @
  --
  -- When you override the default implementation, it must keep the relation to
  -- the other methods:
  --
  -- @
  -- mprodZ 'Nil' === 'one'
  -- mprodZ ('Zee' _) === 'zero'
  -- mprodZ (pure a) = mprodZ ('Cons' a 'Nil') === a
  -- @
  mprodZ :: ZList () a -> a
  mprodZ = mprod . go
    where
      go Nil = []
      go (Zee _) = [zero]
      go (Cons a as) = a : go as

instance DMLZ ()

instance (DMLZ a, DMLZ b) => DMLZ (a, b)