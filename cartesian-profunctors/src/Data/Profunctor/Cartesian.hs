{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Profunctor.Cartesian(
  Cartesian(..),
  prodDay,

  Cocartesian(..),
  sumDay,
  
  -- * @Cartesian p@ iff @forall x. Applicative (p x)@
  pureDefault,
  proUnitDefault,
  liftA2Default,
  fanoutDefault,

  -- * About distributivy laws between 'Cartesian' and 'Cocartesian'
  --
  -- $distributivity
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
import Data.Profunctor.Day

class Profunctor p => Cartesian p where
  {-# MINIMAL proUnit, (proProduct | (***) | (&&&)) #-}

  -- | Unit of the product.
  --
  -- The type of 'proUnit' can be understood as @proUnit' :: p () ()@
  -- treated to have more generally-typed @p a ()@ using 'lmap'.
  -- 
  -- @
  -- const () :: a -> ()
  -- proUnit' :: p () ()
  -- 'lmap' (const ()) proUnit' :: p a ()
  -- @
  proUnit :: p a ()
  
  proProduct :: (a -> (a1,a2)) -> ((b1, b2) -> b) -> p a1 b1 -> p a2 b2 -> p a b
  proProduct f g p q = dimap f g $ p *** q
  
  -- | Product of two profunctors
  (***) :: p a b -> p a' b' -> p (a,a') (b,b')
  p *** q = lmap fst p &&& lmap snd q
  
  -- | Alternative way to define the product (pronounced \"fan-out\")
  (&&&) :: p a b -> p a b' -> p a (b, b')
  (&&&) = proProduct delta id

delta :: a -> (a,a)
delta a = (a,a)

prodDay :: Cartesian r => (p :-> r) -> (q :-> r) -> Day (,) p q :-> r
prodDay pr qr (Day p q opA opB) = proProduct opA opB (pr p) (qr q)

-- * @Cartesian p@ iff @forall x. Applicative (p x)@

pureDefault :: Cartesian p => b -> p a b
pureDefault b = rmap (const b) proUnit

proUnitDefault :: Applicative (p a) => p a ()
proUnitDefault = pure ()

liftA2Default :: Cartesian p => (a -> b -> c) -> p x a -> p x b -> p x c
liftA2Default f = proProduct delta (uncurry f)

fanoutDefault :: (Profunctor p, Applicative (p a)) => p a b1 -> p a b2 -> p a (b1, b2)
fanoutDefault = liftA2 (,)

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
  {-# MINIMAL proEmpty, (proSum | (+++) | (|||)) #-}

  -- | Unit of the sum.
  --
  -- The type of 'proEmpty' can be understood as @proEmpty' :: p Void 'Void'@
  -- treated to have more generally-typed @p Void b@ using 'rmap'.
  -- 
  -- @
  -- 'absurd'    :: Void -> b
  -- proEmpty' :: p Void Void
  -- 'rmap' absurd proEmpty' :: p Void b
  -- @
  proEmpty :: p Void b
  
  proSum :: (a -> Either a1 a2) -> (Either b1 b2 -> b) -> p a1 b1 -> p a2 b2 -> p a b
  proSum f g p q = dimap f g (p +++ q)

  -- | Sum of two profunctors
  (+++) :: p a b -> p a' b' -> p (Either a a') (Either b b')
  p +++ q = rmap Left p ||| rmap Right q

  -- | Alternative way to define the sum (pronounced \"fan-in\")
  (|||) :: p a b -> p a' b -> p (Either a a') b
  (|||) = proSum id nabla

nabla :: Either a a -> a
nabla = either id id

sumDay :: Cocartesian r => (p :-> r) -> (q :-> r) -> Day Either p q :-> r
sumDay pr qr (Day p q opA opB) = proSum opA opB (pr p) (qr q)

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

-- $distributivity
--
-- TODO