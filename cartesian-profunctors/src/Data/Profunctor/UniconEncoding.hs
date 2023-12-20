{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
module Data.Profunctor.UniconEncoding(
  Unicon(..),
  Encoding(..),
  encodeId
) where

import Data.Functor.Classes
import Data.Profunctor (Profunctor(..))
import Data.Profunctor.Cartesian
import Data.Bifunctor (Bifunctor(..))

-- | Universal container. Any container type with finite maximum length and
--   finite number of possible shapes can be encoded into @Unicon@.
data Unicon a = MkUnicon !Int [a]
    deriving stock (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

instance Eq1 Unicon where
  liftEq eq (MkUnicon j as) (MkUnicon k bs) = j == k && liftEq eq as bs

instance Ord1 Unicon where
  liftCompare cmp (MkUnicon j as) (MkUnicon k bs) = compare j k <> liftCompare cmp as bs

-- instance Matchable Unicon

-- | Encoding into @Unicon a@ with partial decoding function.
data Encoding a s t = Encoding Int (s -> Unicon a) (Unicon a -> Maybe (t, [a]))
  deriving stock (Functor)

encodeId :: Encoding a a a
encodeId = Encoding 1 (\a -> MkUnicon 0 [a]) $ \case
    MkUnicon 0 (a : as) -> Just (a, as)
    _ -> Nothing

instance Profunctor (Encoding a) where
  dimap f g (Encoding n enc dec) = Encoding n (enc . f) (fmap (first g) . dec)

instance Cartesian (Encoding a) where
  proUnit = Encoding 1 (const one) matchOne
    where
      one = MkUnicon 0 []
      matchOne (MkUnicon 0 as) = Just ((), as)
      matchOne _ = Nothing

  Encoding m enc dec *** Encoding n enc' dec' = Encoding (n * m) encPair decPair
    where
      encPair (s,s') = case (enc s, enc' s') of
        (MkUnicon j as, MkUnicon k as') -> MkUnicon (j * n + k) (as ++ as')
      decPair (MkUnicon i as)
        | i < 0      = Nothing
        | i >= m * n = Nothing
        | otherwise  = do
              let (j,k) = quotRem i n
              (t1, as') <- dec (MkUnicon j as)
              (t2, as'') <- dec' (MkUnicon k as')
              pure ((t1, t2), as'')

instance Cocartesian (Encoding a) where
  proEmpty = Encoding 0 proEmpty (const Nothing)
  Encoding m enc dec +++ Encoding n enc' dec' = Encoding (m + n) encSum decSum
    where
      encSum (Left s) = enc s
      encSum (Right s') = case enc' s' of
        MkUnicon k as' -> MkUnicon (m + k) as'

      decSum (MkUnicon i as)
        | i < 0 = Nothing
        | i < m = first Left <$> dec (MkUnicon i as)
        | i < m + n = first Right <$> dec' (MkUnicon (i - m) as)
        | otherwise = Nothing