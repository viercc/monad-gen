{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
module Control.Monad.Coproduct(
  -- * Isolated Monad Coproduct
  MonadCoproduct(Pure, Impure, Impure1, Impure2),
  view1, view2, review1, review2,

  inject1, inject2,
  (||||),

  -- * Ideal Monad Coproduct
  (:+)(..),

  -- * Mutual recursion for Ideal monad coproducts
  Mutual (..),
) where

import Control.Monad.Isolate
import Control.Monad.Ideal ((:+)(..))
import Data.Functor.Bind
import qualified Control.Monad.Ideal as Ideal

import Control.Functor.Internal.Mutual (Mutual(..), foldMutual)

data MonadCoproduct m n a =
    Pure a
  | Impure ((Impurity m :+ Impurity n) a)

deriving instance (MonadIsolate m, MonadIsolate n) => Functor (MonadCoproduct m n)

pattern Impure1 :: Mutual Either (Impurity m) (Impurity n) a -> MonadCoproduct m n a
pattern Impure1 mn = Impure (IdealCoproduct (Left mn))

pattern Impure2 :: Mutual Either (Impurity n) (Impurity m) a -> MonadCoproduct m n a
pattern Impure2 mn = Impure (IdealCoproduct (Right mn))

{-# COMPLETE Pure, Impure1, Impure2 #-}

{- |

> MonadCoproduct m n a
>   ~ a + Mutual f g a + Mutual g f a
>   ~ a + f (a + Mutual g f a) + Mutual g f a
>   ~ (a + Mutual g f a) + f (a + Mutual g f a)
>   ~ m (a + Mutual g f a)

-}

view1 :: (MonadIsolate m, MonadIsolate n, f ~ Impurity m, g ~ Impurity n)
  => MonadCoproduct m n a -> m (Either a (Mutual Either g f a))
view1 (Pure a) = pure (Left a)
view1 (Impure1 fg) = injectImpure (runMutual fg)
view1 (Impure2 gf) = pure (Right gf)

review1 :: (MonadIsolate m, MonadIsolate n, f ~ Impurity m, g ~ Impurity n)
  => m (Either a (Mutual Either g f a)) -> MonadCoproduct m n a
review1 mx = case isolatePure mx of
  Left (Left a) -> Pure a
  Left (Right gf) -> Impure2 gf
  Right fx -> Impure1 (Mutual fx)

view2 :: (MonadIsolate m, MonadIsolate n, f ~ Impurity m, g ~ Impurity n)
  => MonadCoproduct m n a -> n (Either a (Mutual Either f g a))
view2 (Pure a) = pure (Left a)
view2 (Impure1 gf) = pure (Right gf)
view2 (Impure2 fg) = injectImpure (runMutual fg)

review2 :: (MonadIsolate m, MonadIsolate n, f ~ Impurity m, g ~ Impurity n)
  => n (Either a (Mutual Either f g a)) -> MonadCoproduct m n a
review2 mx = case isolatePure mx of
  Left (Left a) -> Pure a
  Left (Right gf) -> Impure1 gf
  Right fx -> Impure2 (Mutual fx)

instance (MonadIsolate m, MonadIsolate n) => Apply (MonadCoproduct m n) where
  (<.>) = apDefault

instance (MonadIsolate m, MonadIsolate n) => Applicative (MonadCoproduct m n) where
  pure = Pure
  (<*>) = (<.>)

instance (MonadIsolate m, MonadIsolate n) => Bind (MonadCoproduct m n) where
  (>>-) = (>>=)

instance (MonadIsolate m, MonadIsolate n) => Monad (MonadCoproduct m n) where
  Pure a >>= k = k a
  Impure (IdealCoproduct (Left fg)) >>= k = bindMutual1 fg k
  Impure (IdealCoproduct (Right gf)) >>= k = bindMutual2 gf k

bindMutual1 :: (MonadIsolate m, f ~ Impurity m, MonadIsolate n, g ~ Impurity n)
  => Mutual Either f g a
  -> (a -> MonadCoproduct m n b)
  -> MonadCoproduct m n b
bindMutual1 (Mutual fn) k = review1 $ injectImpure fn >>= view1 . either k (`bindMutual2` k)

bindMutual2 :: (MonadIsolate m, f ~ Impurity m, MonadIsolate n, g ~ Impurity n)
  => Mutual Either g f a
  -> (a -> MonadCoproduct m n b)
  -> MonadCoproduct m n b
bindMutual2 (Mutual fn) k = review2 $ injectImpure fn >>= view2 . either k (`bindMutual1` k)

instance (MonadIsolate m, MonadIsolate n) => MonadIsolate (MonadCoproduct m n) where
  type Impurity (MonadCoproduct m n) = Impurity m :+ Impurity n

  isolatePure (Pure a) = Left a
  isolatePure (Impure mn) = Right mn

  injectImpure = Impure

inject1 :: MonadIsolate m => m a -> MonadCoproduct m n a
inject1 = either Pure (Impure . Ideal.inject1) . isolatePure

inject2 :: MonadIsolate n => n a -> MonadCoproduct m n a
inject2 = either Pure (Impure . Ideal.inject2) . isolatePure

(||||) :: (MonadIsolate m, MonadIsolate n, Monad t)
  => (forall a. m a -> t a)
  -> (forall a. n a -> t a)
  -> MonadCoproduct m n b -> t b
(mt |||| nt) copro = case copro of
  Pure b -> pure b
  Impure1 fg -> foldMutual' mt nt fg
  Impure2 gf -> foldMutual' nt mt gf

foldMutual' :: (MonadIsolate m, MonadIsolate n, Monad t)
  => (forall a. m a -> t a)
  -> (forall a. n a -> t a)
  -> Mutual Either (Impurity m) (Impurity n) b -> t b
foldMutual' mt nt = foldMutual (\ta k -> ta >>= either pure id . k) (mt . injectImpure) (nt . injectImpure)