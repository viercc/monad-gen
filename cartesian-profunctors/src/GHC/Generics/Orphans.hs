{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module GHC.Generics.Orphans where

import GHC.Generics
import Data.Functor.Classes
import Data.Coerce (coerce)

instance Eq1 U1 where
    liftEq _ _ _ = True

instance Ord1 U1 where
    liftCompare _ _ _ = EQ

instance Eq1 V1 where
    liftEq _ v = case v of { }

instance Ord1 V1 where
    liftCompare _ v = case v of { }

instance Eq1 Par1 where
    liftEq = coerce

instance Ord1 Par1 where
    liftCompare = coerce

instance Eq c => Eq1 (K1 i c) where
    liftEq _ (K1 c1) (K1 c2) = c1 == c2

instance Ord c => Ord1 (K1 i c) where
    liftCompare _ (K1 c1) (K1 c2) = compare c1 c2

deriving newtype instance Eq1 f => Eq1 (M1 i m f)
deriving newtype instance Ord1 f => Ord1 (M1 i m f)
deriving newtype instance Eq1 f => Eq1 (Rec1 f)
deriving newtype instance Ord1 f => Ord1 (Rec1 f)

instance (Eq1 f, Eq1 g) => Eq1 (f :+: g) where
    liftEq eq = eq'
      where
        eq' (L1 fa) (L1 fb) = liftEq eq fa fb
        eq' (R1 ga) (R1 gb) = liftEq eq ga gb
        eq' _ _ = False

instance (Ord1 f, Ord1 g) => Ord1 (f :+: g) where
    liftCompare cmp = cmp'
      where
        cmp' (L1 fa) (L1 fb) = liftCompare cmp fa fb
        cmp' (L1 _) (R1 _) = LT
        cmp' (R1 _) (L1 _) = GT
        cmp' (R1 ga) (R1 gb) = liftCompare cmp ga gb

instance (Eq1 f, Eq1 g) => Eq1 (f :*: g) where
    liftEq eq (fa :*: ga) (fb :*: gb) = liftEq eq fa fb && liftEq eq ga gb

instance (Ord1 f, Ord1 g) => Ord1 (f :*: g) where
    liftCompare cmp (fa :*: ga) (fb :*: gb) = liftCompare cmp fa fb <> liftCompare cmp ga gb

instance (Eq1 f, Eq1 g) => Eq1 (f :.: g) where
    liftEq eq (Comp1 fga) (Comp1 fgb) = liftEq (liftEq eq) fga fgb

instance (Ord1 f, Ord1 g) => Ord1 (f :.: g) where
    liftCompare cmp (Comp1 fga) (Comp1 fgb) = liftCompare (liftCompare cmp) fga fgb

instance (Generic1 t, Foldable (Rep1 t)) => Foldable (Generically1 t) where
    foldMap f (Generically1 ta) = foldMap f (from1 ta)

instance (Generic1 t, Traversable (Rep1 t)) => Traversable (Generically1 t) where
    traverse f (Generically1 ta) = Generically1 . to1 <$> traverse f (from1 ta)