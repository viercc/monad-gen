{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
module Data.Profunctor.UniconEncoding(
  Unicon(..), Builder(), build,

  Encoding(..),
  encodeWith, decodeWith,
  idEncoding
) where

import Data.Functor.Classes
import Data.Profunctor (Profunctor(..))
import Data.Profunctor.Cartesian
import Data.Bifunctor (Bifunctor(..))

import Data.Vector (Vector)
import qualified Data.Vector as V
import Control.Monad (guard)

-- | Universal container. Any container type with finite maximum length and
--   finite number of possible shapes can be encoded into @Unicon@.
data Unicon a = MkUnicon !Int !(Vector a)
    deriving stock (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

instance Eq1 Unicon where
  liftEq eq (MkUnicon j as) (MkUnicon k bs) = j == k && liftEq eq as bs

instance Ord1 Unicon where
  liftCompare cmp (MkUnicon j as) (MkUnicon k bs) = compare j k <> liftCompare cmp as bs

-- | A lazy version of 'Unicon'.
--
--   This type is meant to be abstract. Only thing you can do is
--   to convert it into @Unicon@ using 'build'. 
data Builder a = Builder !Int (B a)

build :: Builder a -> Unicon a
build (Builder n as) = MkUnicon n (V.fromList (buildList as))

data B a = Empty | Singleton a | Append (B a) (B a)
  deriving (Functor, Foldable, Traversable)

buildList :: B a -> [a]
buildList as = case as of
  Empty -> []
  Singleton a -> [a]
  Append as1 as2 -> case as1 of
    Empty -> buildList as2
    Singleton a      -> a : buildList as2
    Append as11 as12 -> buildList (Append as11 (Append as12 as2))

-- | Encoding into @Unicon a@ with partial decoding function.
data Encoding a b s t = Encoding Int (s -> Builder a) (Unicon b -> Maybe (t, Vector b))
  deriving stock (Functor)

encodeWith :: Encoding a b s t -> s -> Unicon a
encodeWith (Encoding _ enc _) = build . enc

decodeWith :: Encoding a b s t -> Unicon b -> Maybe t
decodeWith (Encoding _ _ dec) = fmap fst . dec

idEncoding :: Encoding a b a b
idEncoding = Encoding 1 enc dec
  where
    enc :: a -> Builder a
    enc a = Builder 0 (Singleton a)

    dec :: Unicon b -> Maybe (b, Vector b)
    dec (MkUnicon tag bs) = do
      guard $ tag == 0
      V.uncons bs

instance Profunctor (Encoding a b) where
  dimap f g (Encoding n enc dec) = Encoding n (enc . f) (fmap (first g) . dec)

instance Cartesian (Encoding a b) where
  proUnit = Encoding 1 (const one) matchOne
    where
      one = Builder 0 Empty
      matchOne (MkUnicon 0 bs) = Just ((), bs)
      matchOne _ = Nothing

  Encoding m enc dec *** Encoding n enc' dec' = Encoding (n * m) encPair decPair
    where
      encPair (s,s') = case (enc s, enc' s') of
        (Builder j as, Builder k as') -> Builder (j * n + k) (Append as as')
      decPair (MkUnicon i bs)
        | i < 0      = Nothing
        | i >= m * n = Nothing
        | otherwise  = do
              let (j,k) = quotRem i n
              (t1, bs') <- dec (MkUnicon j bs)
              (t2, bs'') <- dec' (MkUnicon k bs')
              pure ((t1, t2), bs'')

instance Cocartesian (Encoding a b) where
  proEmpty = Encoding 0 proEmpty (const Nothing)
  Encoding m enc dec +++ Encoding n enc' dec' = Encoding (m + n) encSum decSum
    where
      encSum (Left s) = enc s
      encSum (Right s') = case enc' s' of
        Builder k bs' -> Builder (m + k) bs'

      decSum (MkUnicon i bs)
        | i < 0 = Nothing
        | i < m = first Left <$> dec (MkUnicon i bs)
        | i < m + n = first Right <$> dec' (MkUnicon (i - m) bs)
        | otherwise = Nothing