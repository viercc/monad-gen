module Data.DoubleMonoid.LZ.Class where

import Data.DoubleMonoid.Class

import Data.List.ZList ( ZList(..) )

-- | Double monoid with additional property (/left zero/):
--   'zero' is a right-absorbing element.
--
-- @
-- zero <> x = zero
-- @
class DoubleMonoid a => DMLZ a where
  {-# MINIMAL #-}

  -- | @mprodZ@ is a @ZList@ algebra.
  -- 
  -- @
  -- mprodZ . fmap mprodZ === mprodZ . 'Control.Monad.join'
  -- @
  -- 
  -- When you override the default implementation, it must keep the relation to
  -- the other methods:
  -- 
  -- @
  -- mprodZ 'Nend' === 'one'
  -- mprodZ 'Zend' === 'zero'
  -- mprodZ (pure a) = mprodZ ('Cons' a 'Nend') === a
  -- @
  mprodZ :: ZList a -> a
  mprodZ = mprod . go
    where
      go Nend = []
      go Zend = [zero]
      go (Cons a as) = a : go as

instance DMLZ ()
instance (DMLZ a, DMLZ b) => DMLZ (a,b)
instance Monoid a => DMLZ (Maybe a)
instance Monoid a => DMLZ [a]