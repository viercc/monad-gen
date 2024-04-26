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
-- Given two @'Isolated' m@ and @Isolated n@, the functor @m :+ n@ is @Isolated@ too. In other words,
-- given two @Monad@s @Unite m@ and @Unite n@, this type constructs new @Monad (Unite (m :+ n))@.
--
-- Furthermore, as the name suggests,
-- @Unite (m :+ n)@ is the coproduct of @Unite m@ and @Unite n@ as a @Monad@.
--
-- - @'hoistUnite' 'inject1' :: Unite m ~> Unite (m :+ n)@ is a monad morphism
-- - @'hoistUnite' 'inject2' :: Unite n ~> Unite (m :+ n)@ is a monad morphism
-- - @'eitherMonad' mt nt :: (m :+ n) ~> t@ is a impure monad morphism,
--   given @(mt :: m ~> t)@ and @(nt :: n ~> t)@ are impure monad morphisms.
-- - Any impure monad morphisms @(m :+ n) ~> t@ can be uniquely rewritten as @(eitherMonad mt nt)@.
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
-- Given two @'MonadIdeal' m@ and @MonadIdeal n@, the functor @m :+ n@ is @MonadIdeal@ too.
-- It is the coproduct of @m@ and @n@ as a @MonadIdeal@.
--
-- - @inject1 :: m ~> (m :+ n)@ is a @MonadIdeal@ morphism
-- - @inject2 :: n ~> (m :+ n)@ is a @MonadIdeal@ morphism
-- - @(mt |||| nt) :: (m :+ n) ~> t@ is a @MonadIdeal@ morphism, given
--   @mt, nt@ are @MonadIdeal@ morphisms.
-- - Any @MonadIdeal@ morphism @(m :+ n) ~> t@ can be uniquely rewritten as @(mt |||| nt)@.
--
-- Here, a @MonadIdeal@ morphism is a natural transformation @nat@ between @MonadIdeal@ such that
-- preserves @idealBind@.
-- 
-- @
-- nat (idealBind ma k) = idealBind (nat ma) ('hoistIdeal' nat . k)
-- @
-- 
newtype (:+) m n a = Coproduct { runCoproduct :: Either (Mutual Either m n a) (Mutual Either n m a) }

inject1 :: (Functor m) => m a -> (m :+ n) a
inject1 = Coproduct . Left . Mutual . fmap Left

inject2 :: (Functor n) => n a -> (m :+ n) a
inject2 = Coproduct . Right . Mutual . fmap Left

instance (Functor m, Functor n) => Functor (m :+ n) where
  fmap f = Coproduct . bimap (fmap f) (fmap f) . runCoproduct

instance (MonadIdeal m, MonadIdeal n) => Apply (m :+ n) where
  (<.>) = apDefault

instance (MonadIdeal m, MonadIdeal n) => Bind (m :+ n) where
  (>>-) = bindDefault

instance (Isolated m, Isolated n) => Isolated (m :+ n) where
  impureBind copro k = case runCoproduct copro of
    Left mn -> imbindMutual1 mn k
    Right nm -> imbindMutual2 nm k

instance (MonadIdeal m, MonadIdeal n) => MonadIdeal (m :+ n) where
  idealBind copro k = Coproduct $ case runCoproduct copro of
    Left mn -> Left $ bindMutual1 mn k
    Right nm -> Right $ bindMutual2 nm k

bindMutual1 :: (MonadIdeal m, MonadIdeal n) => Mutual Either m n a -> (a -> Ideal (m :+ n) b) -> Mutual Either m n b
bindMutual1 (Mutual mn) k =
  Mutual $
    mn `idealBind` \next ->
      case next of
        Left a -> case runIdeal (k a) of
          Left b -> pure (Left b)
          Right (Coproduct (Left mn')) -> ideal . Right $ runMutual mn'
          Right (Coproduct (Right nm')) -> pure (Right nm')
        Right nm -> pure . Right $ bindMutual2 nm k

bindMutual2 :: (MonadIdeal m, MonadIdeal n) => Mutual Either m n a -> (a -> Ideal (n :+ m) b) -> Mutual Either m n b
bindMutual2 (Mutual mn) k =
  Mutual $
    mn `idealBind` \next ->
      case next of
        Left a -> case runIdeal (k a) of
          Left b -> pure (Left b)
          Right (Coproduct (Left nm')) -> pure (Right nm')
          Right (Coproduct (Right mn')) -> ideal . Right $ runMutual mn'
        Right nm -> pure . Right $ bindMutual1 nm k

(||||) :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> (m :+ n) b -> t b
mt |||| nt = either (foldMutual' mt nt) (foldMutual' nt mt) . runCoproduct

foldMutual' :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> Mutual Either m n b -> t b
foldMutual' = foldMutual (\ta k -> ta `idealBind` ideal . k)



{- |

> MonadCoproduct m n a
>   ~ a + Mutual f g a + Mutual g f a
>   ~ a + f (a + Mutual g f a) + Mutual g f a
>   ~ (a + Mutual g f a) + f (a + Mutual g f a)
>   ~ m (a + Mutual g f a)

-}

imbindMutual1 :: (Isolated m, Isolated n)
  => Mutual Either m n a
  -> (a -> Unite (m :+ n) b)
  -> Unite (m :+ n) b
imbindMutual1 (Mutual mna) k =
  review1 $ impureBind mna $ \na -> case na of
    Left a -> view1 (k a)
    Right na' -> view1 (imbindMutual2 na' k)

imbindMutual2 :: (Isolated m, Isolated n)
  => Mutual Either n m a
  -> (a -> Unite (m :+ n) b)
  -> Unite (m :+ n) b
imbindMutual2 (Mutual nma) k =
  review2 $ impureBind nma $ \ma -> case ma of
    Left a -> view2 (k a)
    Right ma' -> view2 (imbindMutual1 ma' k)

view1 :: Unite (m :+ n) a -> Unite m (Either a (Mutual Either n m a))
view1 (Unite (Left a)) = Unite (Left (Left a))
view1 (Unite (Right copro)) = case runCoproduct copro of
  Left mn -> Unite (Right (runMutual mn))
  Right nm -> Unite (Left (Right nm))

review1 :: Unite m (Either a (Mutual Either n m a)) -> Unite (m :+ n) a 
review1 (Unite (Left (Left a))) = Unite (Left a)
review1 (Unite (Left (Right nm))) = Unite (Right (Coproduct (Right nm)))
review1 (Unite (Right mn)) = Unite (Right (Coproduct (Left (Mutual mn))))

view2 :: Unite (m :+ n) a -> Unite n (Either a (Mutual Either m n a))
view2 (Unite (Left a)) = Unite (Left (Left a))
view2 (Unite (Right copro)) = case runCoproduct copro of
  Left mn -> Unite (Left (Right mn))
  Right nm -> Unite (Right (runMutual nm))

review2 :: Unite n (Either a (Mutual Either m n a)) -> Unite (m :+ n) a 
review2 (Unite (Left (Left a))) = Unite (Left a)
review2 (Unite (Left (Right mn))) = Unite (Right (Coproduct (Left mn)))
review2 (Unite (Right nm)) = Unite (Right (Coproduct (Right (Mutual nm))))

eitherMonad :: (Isolated m, Isolated n, Monad t)
  => (forall a. m a -> t a)
  -> (forall a. n a -> t a)
  -> (m :+ n) b -> t b
eitherMonad mt nt copro = case runCoproduct copro of
  Left fg -> foldMutual'' mt nt fg
  Right gf -> foldMutual'' nt mt gf

foldMutual'' :: (Monad t)
  => (forall a. m a -> t a)
  -> (forall a. n a -> t a)
  -> Mutual Either m n b -> t b
foldMutual'' = foldMutual (\ta k -> ta >>= either pure id . k)