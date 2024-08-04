module Data.DoubleMonoid.LZLC.Class where

import Data.DoubleMonoid.Class
import Data.DoubleMonoid.LZ.Class
import Data.List.ZList

-- | 'DoubleMonoid' with left zero ('DMLZ') and left catch
--
-- @
-- -- left catch
-- one \/+\/ x === one
-- @
class DMLZ a => DMLZLC a where
  {-# MINIMAL #-}
  
  -- | @('zero', '/+/')@ is a monoid with a right zero element @one@.
  --   This can be stated as @msumZ@ is a @ZList@ algebra.
  -- 
  -- @
  -- msumZ . fmap msumZ === msumZ . 'Control.Monad.join'
  -- @
  -- 
  -- When you override the default implementation, it must keep the relation to
  -- the other methods:
  -- 
  -- @
  -- msumZ 'Nend' === 'zero'
  -- msumZ 'Zend' === 'one'
  -- mprodZ ('Cons' a 'Nend') === a
  -- @
  msumZ :: ZList a -> a
  msumZ = msum . go
    where
      go Nend = []
      go Zend = [one]
      go (Cons a as) = a : go as

