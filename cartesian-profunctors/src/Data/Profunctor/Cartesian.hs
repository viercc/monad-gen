module Data.Profunctor.Cartesian(
  Cartesian(..),
  Cocartesian(..),
  (&&&),
  (|||)
) where

import Control.Applicative

import Data.Void

import Data.Functor.Contravariant.Divisible
import Data.Bifunctor(Bifunctor(..))
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Profunctor
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Data.Profunctor.Composition

class Profunctor p => Cartesian p where
  proUnit :: p a ()
  (***) :: p a b -> p a' b' -> p (a,a') (b,b')

delta :: a -> (a,a)
delta a = (a,a)

(&&&) :: Cartesian p => p a b -> p a b' -> p a (b, b')
p1 &&& p2 = lmap delta (p1 *** p2)

instance Cartesian (->) where
  proUnit = const ()
  p1 *** p2 = bimap p1 p2

instance (Monoid r) => Cartesian (Forget r) where
  proUnit = Forget (const mempty)
  Forget f *** Forget g = Forget (\(a,b) -> f a <> g b)

instance (Applicative f) => Cartesian (Star f) where
  proUnit = Star (const (pure ()))
  Star p1 *** Star p2 = Star $ \(a,a') -> liftA2 (,) (p1 a) (p2 a')

instance (Applicative f) => Cartesian (Joker f) where
  proUnit = Joker (pure ())
  Joker p1 *** Joker p2 = Joker $ liftA2 (,) p1 p2

instance (Divisible f) => Cartesian (Clown f) where
  proUnit = Clown conquer
  Clown p1 *** Clown p2 = Clown $ divided p1 p2

instance (Cartesian p, Cartesian q) => Cartesian (Product p q) where
  proUnit = Pair proUnit proUnit
  Pair p1 q1 *** Pair p2 q2 = Pair (p1 *** p2) (q1 *** q2)

instance (Cartesian p, Cartesian q) => Cartesian (Procompose p q) where
  proUnit = Procompose proUnit proUnit
  Procompose p1 q1 *** Procompose p2 q2 =
    Procompose (p1 *** p2) (q1 *** q2)

instance (Cartesian p) => Cartesian (Yoneda p) where
  proUnit = proreturn proUnit
  p *** q = proreturn (proextract p *** proextract q)

instance (Cartesian p) => Cartesian (Coyoneda p) where
  proUnit = proreturn proUnit
  Coyoneda l1 r1 p *** Coyoneda l2 r2 q
    = Coyoneda (l1 *** l2) (r1 *** r2) (p *** q)

class Profunctor p => Cocartesian p where
  proEmpty :: p Void a
  (+++) :: p a b -> p a' b' -> p (Either a a') (Either b b')

nabla :: Either a a -> a
nabla = either id id

(|||) :: (Cocartesian p) => p a b -> p a' b -> p (Either a a') b
p1 ||| p2 = rmap nabla (p1 +++ p2)

instance Cocartesian (->) where
  proEmpty = absurd
  p1 +++ p2 = bimap p1 p2

instance Cocartesian (Forget r) where
  proEmpty = Forget absurd
  Forget f +++ Forget g = Forget (either f g)

instance (Functor f) => Cocartesian (Star f) where
  proEmpty = Star absurd
  Star p1 +++ Star p2 = Star $ either (fmap Left . p1) (fmap Right . p2)

instance (Alternative f) => Cocartesian (Joker f) where
  proEmpty = Joker empty
  Joker p1 +++ Joker p2 = Joker $ (Left <$> p1) <|> (Right <$> p2)

instance (Decidable f) => Cocartesian (Clown f) where
  proEmpty = Clown lost
  Clown p1 +++ Clown p2 = Clown $ chosen p1 p2

instance (Cocartesian p, Cocartesian q)
       => Cocartesian (Product p q) where
  proEmpty = Pair proEmpty proEmpty
  Pair p1 q1 +++ Pair p2 q2 = Pair (p1 +++ p2) (q1 +++ q2)

instance (Cocartesian p, Cocartesian q)
       => Cocartesian (Procompose p q) where
  proEmpty = Procompose proEmpty proEmpty
  Procompose p1 q1 +++ Procompose p2 q2 = Procompose (p1 +++ p2) (q1 +++ q2)

instance (Cocartesian p) => Cocartesian (Yoneda p) where
  proEmpty = proreturn proEmpty
  p +++ q = proreturn (proextract p +++ proextract q)

instance (Cocartesian p) => Cocartesian (Coyoneda p) where
  proEmpty = proreturn proEmpty
  Coyoneda l1 r1 p +++ Coyoneda l2 r2 q
    = Coyoneda (l1 +++ l2) (r1 +++ r2) (p +++ q)
