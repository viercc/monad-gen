module Data.DoubleMonoid.LZ.Class where

import Data.DoubleMonoid.Class

import Data.List.ZList

-- | Double monoid with left zero property
--
-- @
-- zero /*/ x = zero
-- @
class DoubleMonoid a => DMLZ a where
  {-# MINIMAL #-}

  -- | @('one', '/*/')@ is a monoid with one right zero element 'zero'.
  --   This can be stated as @mprodZ@ is a @ZList@ algebra.
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
  -- mprodZ ('Cons' a 'Nend') === a
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