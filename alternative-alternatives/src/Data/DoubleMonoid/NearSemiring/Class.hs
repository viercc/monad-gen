module Data.DoubleMonoid.NearSemiring.Class where

import Data.DoubleMonoid.LZ.Class (DMLZ)

-- | 'NearSemiring' is law-only subclass of
--   'Data.DoubleMonoid.Class.DoubleMonoid'
--   with additional /left zero/ law (hence 'DMLZ') and
--   /left distribution/ law.
-- 
-- @
-- -- Left distribution
-- -- (it is called "right distributivity" more commonly)
-- (x <+> y) <> z === (x <> z) <+> (y <> z)
-- @
class DMLZ a => NearSemiring a

instance NearSemiring ()
instance (NearSemiring a, NearSemiring b) => NearSemiring (a,b)
instance Monoid a => NearSemiring (Maybe a)
instance Monoid a => NearSemiring [a]