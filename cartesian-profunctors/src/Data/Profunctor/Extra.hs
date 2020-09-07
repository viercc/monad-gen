{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
module Data.Profunctor.Extra where

import Data.Void
import Data.Coerce

import Control.Applicative

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Bifunctor(bimap)
import Data.Bifunctor.Clown
import Data.Profunctor
import Data.Profunctor.Cartesian

type EquivalenceP = Clown Equivalence
type ComparisonP = Clown Comparison

-- | Basically 'Data.Profunctor.Coyoneda' ('Star' f) but a bit efficient,
--   and isomorphic to Star f if f is covariant Functor.
--
--   Unlike directly using 'Star', two arguments of 'CoYoStar f' is
--   always representational.
data CoYoStar f a b where
  CoYoStar :: (c -> b) -> (a -> f c) -> CoYoStar f a b

liftCoYoStar :: (a -> f b) -> CoYoStar f a b
liftCoYoStar = CoYoStar id

lowerCoYoStar :: (Functor f) => CoYoStar f a b -> a -> f b
lowerCoYoStar (CoYoStar g f) = fmap g . f

instance Profunctor (CoYoStar f) where
  dimap l r (CoYoStar g f) = CoYoStar (r . g) (f . l)

instance (Applicative f) => Cartesian (CoYoStar f) where
  proUnit = liftCoYoStar (const (pure ()))
  CoYoStar g f *** CoYoStar g' f' = CoYoStar id h
    where
      u c c' = (g c, g' c')
      h (a, a') = liftA2 u (f a) (f' a')

instance (Functor f) => Cocartesian (CoYoStar f) where
  proEmpty = liftCoYoStar absurd
  CoYoStar g f +++ CoYoStar g' f' = CoYoStar id h
    where
      h = either (fmap (Left . g) . f) (fmap (Right . g') . f')

-- | > CoYoJoker f ~ Joker (Coyoneda f)
--   
--   where Coyoneda is from Data.Functor.Coyoneda in "kan-extensions".
--   But since it's simple, I don't think it's necessary to depend on kan-extensions.
--  
--   Unlike directly using 'Joker', the second argument of 'CoYoJoker f' is
--   always representational.
data CoYoJoker f a b where
  CoYoJoker :: (c -> b) -> f c -> CoYoJoker f a b

liftCoYoJoker :: f b -> CoYoJoker f a b
liftCoYoJoker = CoYoJoker id

lowerCoYoJoker :: (Functor f) => CoYoJoker f a b -> f b
lowerCoYoJoker (CoYoJoker g f) = fmap g f

instance Profunctor (CoYoJoker f) where
  dimap _ r (CoYoJoker g f) = CoYoJoker (r . g) f
  lmap _ = coerce
  rmap r (CoYoJoker g f) = CoYoJoker (r . g) f

instance (Applicative f) => Cartesian (CoYoJoker f) where
  proUnit = liftCoYoJoker (pure ())
  CoYoJoker g f *** CoYoJoker g' f' = CoYoJoker id h
    where
      h = liftA2 (\a a' -> (g a, g' a')) f f'

instance (Alternative f) => Cocartesian (CoYoJoker f) where
  proEmpty = liftCoYoJoker empty
  CoYoJoker g f +++ CoYoJoker g' f' = CoYoJoker id h
    where
      h = (Left . g <$> f) <|> (Right . g' <$> f')

-- | > CoYoClown f ~ Clown (Coyoneda f)
--   
--   where Coyoneda is from Data.Functor.Contravariant.Coyoneda in "kan-extensions".
--   But since it's simple, I don't think it's necessary to depend on kan-extensions.
--  
--   Unlike directly using 'Clown', the first argument of 'CoYoClown f' is
--   always representational.
data CoYoClown f a b where
  CoYoClown :: (a -> c) -> f c -> CoYoClown f a b

liftCoYoClown :: f a -> CoYoClown f a b
liftCoYoClown = CoYoClown id

lowerCoYoClown :: (Contravariant f) => CoYoClown f a b -> f a
lowerCoYoClown (CoYoClown g f) = contramap g f

instance Profunctor (CoYoClown f) where
  dimap l _ (CoYoClown g f) = CoYoClown (g . l) f
  lmap l (CoYoClown g f) = CoYoClown (g . l) f
  rmap _ = coerce

instance (Divisible f) => Cartesian (CoYoClown f) where
  proUnit = liftCoYoClown conquer
  CoYoClown g f *** CoYoClown g' f' = CoYoClown id h
    where
      h = divide (bimap g g') f f'

instance (Decidable f) => Cocartesian (CoYoClown f) where
  proEmpty = liftCoYoClown lost
  CoYoClown g f +++ CoYoClown g' f' = CoYoClown id h
    where
      h = choose (bimap g g') f f'
