module Data.DoubleMonoid.LZ where

import Data.DoubleMonoid

-- | Double monoid with left zero property
--
-- @
-- zero /*/ x = zero
-- @
class DoubleMonoid a => DMLZ a where
  {-# MINIMAL #-}

  