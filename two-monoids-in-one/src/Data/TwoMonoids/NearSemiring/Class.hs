module Data.TwoMonoids.NearSemiring.Class where

import Data.TwoMonoids.LZ.Class (DMLZ)

-- | 'NearSemiring' is law-only subclass of
--   'Data.TwoMonoids.Class.TwoMonoids'
--   with additional /left zero/ law (hence 'DMLZ') and
--   /left distribution/ law.
--
-- @
-- -- Left distribution
-- -- (it is called "right distributivity" more commonly)
-- (x <+> y) <> z === (x <> z) <+> (y <> z)
-- @
class (DMLZ a) => NearSemiring a

instance NearSemiring ()

instance (NearSemiring a, NearSemiring b) => NearSemiring (a, b)