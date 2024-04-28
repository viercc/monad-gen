{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Coproduct
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
module Control.Monad.Coproduct(
  -- * Ideal Monad Coproduct
  (:+)(..),
  inject1,
  inject2,
  (||||),
  eitherMonad,

  -- * Mutual recursion for ideal monad coproducts
  Mutual (..),
) where

import Data.Functor.Bind
import Control.Monad.Isolated
import Control.Monad.Ideal
import Control.Functor.Internal.Mutual (Mutual(..), foldMutual)

import Data.Bifunctor (Bifunctor(..))

-- * Coproduct of Monads

-- | Coproduct of (impure parts of) two Monads.
-- 
-- === As the coproduct of 'Isolated'
-- 
-- Given @'Isolated' m0@ and @Isolated n0@, the functor @m0 :+ n0@ is @Isolated@ too. In other words,
-- given two @Monad@s @Unite m0@ and @Unite n0@, this type constructs a new @Monad (Unite (m0 :+ n0))@.
--
-- Furthermore, as the name suggests,
-- @Unite (m0 :+ n0)@ is the coproduct of @Unite m0@ and @Unite n0@ as a @Monad@.
--
-- - @'hoistUnite' 'inject1' :: Unite m0 ~> Unite (m0 :+ n0)@ is a monad morphism
-- - @'hoistUnite' 'inject2' :: Unite n0 ~> Unite (m0 :+ n0)@ is a monad morphism
-- - @'eitherMonad' mt nt :: (m0 :+ n0) ~> t@ is an impure monad morphism,
--   given @(mt :: m0 ~> t)@ and @(nt :: n0 ~> t)@ are impure monad morphisms.
-- - Any impure monad morphisms @(m0 :+ n0) ~> t@ can be uniquely rewritten as @(eitherMonad mt nt)@.
--
-- Here, a natural transformation @nat :: f ~> g@ is an /impure monad morphism/ means
-- @f@ is an @Isolated@, @g@ is a @Monad@, and @nat@ becomes a monad morphism when combined with @pure@ as below.
--
-- @
-- either pure nat . runUnite :: Unite f ~> g
-- @
--
-- === As the coproduct of 'MonadIdeal'
-- 
-- Given @'MonadIdeal' m0@ and @MonadIdeal n0@, the functor @m0 :+ n0@ is @MonadIdeal@ too.
-- It is the coproduct of @m0@ and @n0@ as a @MonadIdeal@.
--
-- - @inject1 :: m0 ~> (m0 :+ n0)@ is a @MonadIdeal@ morphism
-- - @inject2 :: n0 ~> (m0 :+ n0)@ is a @MonadIdeal@ morphism
-- - @(mt |||| nt) :: (m0 :+ n0) ~> t0@ is a @MonadIdeal@ morphism, given
--   @mt, nt@ are @MonadIdeal@ morphisms.
-- - Any @MonadIdeal@ morphism @(m0 :+ n0) ~> t0@ can be uniquely rewritten as @(mt |||| nt)@.
--
-- Here, a @MonadIdeal@ morphism is a natural transformation @nat@ between @MonadIdeal@ such that
-- preserves @idealBind@.
-- 
-- @
-- nat (idealBind ma k) = idealBind (nat ma) ('hoistIdeal' nat . k)
-- @
-- 
newtype (:+) m0 n0 a = Coproduct { runCoproduct :: Either (Mutual Either m0 n0 a) (Mutual Either n0 m0 a) }

inject1 :: (Functor m0) => m0 a -> (m0 :+ n0) a
inject1 = Coproduct . Left . Mutual . fmap Left

inject2 :: (Functor n0) => n0 a -> (m0 :+ n0) a
inject2 = Coproduct . Right . Mutual . fmap Left

instance (Functor m0, Functor n0) => Functor (m0 :+ n0) where
  fmap f = Coproduct . bimap (fmap f) (fmap f) . runCoproduct

instance (MonadIdeal m0, MonadIdeal n0) => Apply (m0 :+ n0) where
  (<.>) = apDefault

instance (MonadIdeal m0, MonadIdeal n0) => Bind (m0 :+ n0) where
  (>>-) = bindDefault

instance (Isolated m0, Isolated n0) => Isolated (m0 :+ n0) where
  impureBind copro k = case runCoproduct copro of
    Left mn -> imbindMutual1 mn k
    Right nm -> imbindMutual2 nm k

instance (MonadIdeal m0, MonadIdeal n0) => MonadIdeal (m0 :+ n0) where
  idealBind copro k = Coproduct $ case runCoproduct copro of
    Left mn -> Left $ bindMutual1 mn k
    Right nm -> Right $ bindMutual2 nm k

bindMutual1 :: (MonadIdeal m0, MonadIdeal n0) => Mutual Either m0 n0 a -> (a -> Ideal (m0 :+ n0) b) -> Mutual Either m0 n0 b
bindMutual1 (Mutual mn) k =
  Mutual $
    mn `idealBind` \next ->
      case next of
        Left a -> case runIdeal (k a) of
          Left b -> pure (Left b)
          Right (Coproduct (Left mn')) -> ideal . Right $ runMutual mn'
          Right (Coproduct (Right nm')) -> pure (Right nm')
        Right nm -> pure . Right $ bindMutual2 nm k

bindMutual2 :: (MonadIdeal m0, MonadIdeal n0) => Mutual Either m0 n0 a -> (a -> Ideal (n0 :+ m0) b) -> Mutual Either m0 n0 b
bindMutual2 (Mutual mn) k =
  Mutual $
    mn `idealBind` \next ->
      case next of
        Left a -> case runIdeal (k a) of
          Left b -> pure (Left b)
          Right (Coproduct (Left nm')) -> pure (Right nm')
          Right (Coproduct (Right mn')) -> ideal . Right $ runMutual mn'
        Right nm -> pure . Right $ bindMutual1 nm k

(||||) :: (MonadIdeal t) => (forall a. m0 a -> t a) -> (forall a. n0 a -> t a) -> (m0 :+ n0) b -> t b
mt |||| nt = either (foldMutual' mt nt) (foldMutual' nt mt) . runCoproduct

foldMutual' :: (MonadIdeal t) => (forall a. m0 a -> t a) -> (forall a. n0 a -> t a) -> Mutual Either m0 n0 b -> t b
foldMutual' = foldMutual (\ta k -> ta `idealBind` ideal . k)



{- |

> MonadCoproduct m0 n0 a
>   ~ a + Mutual f g a + Mutual g f a
>   ~ a + f (a + Mutual g f a) + Mutual g f a
>   ~ (a + Mutual g f a) + f (a + Mutual g f a)
>   ~ m0 (a + Mutual g f a)

-}

imbindMutual1 :: (Isolated m0, Isolated n0)
  => Mutual Either m0 n0 a
  -> (a -> Unite (m0 :+ n0) b)
  -> Unite (m0 :+ n0) b
imbindMutual1 (Mutual mna) k =
  review1 $ impureBind mna $ \na -> case na of
    Left a -> view1 (k a)
    Right na' -> view1 (imbindMutual2 na' k)

imbindMutual2 :: (Isolated m0, Isolated n0)
  => Mutual Either n0 m0 a
  -> (a -> Unite (m0 :+ n0) b)
  -> Unite (m0 :+ n0) b
imbindMutual2 (Mutual nma) k =
  review2 $ impureBind nma $ \ma -> case ma of
    Left a -> view2 (k a)
    Right ma' -> view2 (imbindMutual1 ma' k)

view1 :: Unite (m0 :+ n0) a -> Unite m0 (Either a (Mutual Either n0 m0 a))
view1 (Unite (Left a)) = Unite (Left (Left a))
view1 (Unite (Right copro)) = case runCoproduct copro of
  Left mn -> Unite (Right (runMutual mn))
  Right nm -> Unite (Left (Right nm))

review1 :: Unite m0 (Either a (Mutual Either n0 m0 a)) -> Unite (m0 :+ n0) a 
review1 (Unite (Left (Left a))) = Unite (Left a)
review1 (Unite (Left (Right nm))) = Unite (Right (Coproduct (Right nm)))
review1 (Unite (Right mn)) = Unite (Right (Coproduct (Left (Mutual mn))))

view2 :: Unite (m0 :+ n0) a -> Unite n0 (Either a (Mutual Either m0 n0 a))
view2 (Unite (Left a)) = Unite (Left (Left a))
view2 (Unite (Right copro)) = case runCoproduct copro of
  Left mn -> Unite (Left (Right mn))
  Right nm -> Unite (Right (runMutual nm))

review2 :: Unite n0 (Either a (Mutual Either m0 n0 a)) -> Unite (m0 :+ n0) a 
review2 (Unite (Left (Left a))) = Unite (Left a)
review2 (Unite (Left (Right mn))) = Unite (Right (Coproduct (Left mn)))
review2 (Unite (Right nm)) = Unite (Right (Coproduct (Right (Mutual nm))))

eitherMonad :: (Isolated m0, Isolated n0, Monad t)
  => (forall a. m0 a -> t a)
  -> (forall a. n0 a -> t a)
  -> (m0 :+ n0) b -> t b
eitherMonad mt nt copro = case runCoproduct copro of
  Left fg -> foldMutual'' mt nt fg
  Right gf -> foldMutual'' nt mt gf

foldMutual'' :: (Monad t)
  => (forall a. m0 a -> t a)
  -> (forall a. n0 a -> t a)
  -> Mutual Either m0 n0 b -> t b
foldMutual'' = foldMutual (\ta k -> ta >>= either pure id . k)