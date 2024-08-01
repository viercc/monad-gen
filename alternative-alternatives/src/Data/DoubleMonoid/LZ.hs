module Data.DoubleMonoid.LZ where

import Data.DoubleMonoid

import Data.List.ZList

-- | Double monoid with left zero property
--
-- @
-- zero /*/ x = zero
-- @
class DoubleMonoid a => DMLZ a where
  {-# MINIMAL #-}

  -- | @('one', '/*/', 'zero')@ is a monoid with one left zero element.
  --   This can be stated as @a@ is a @ZList@ algebra.
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