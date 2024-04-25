
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Ideal
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Monad.Ideal
  ( -- * Ideal Monads
    MonadIdeal (..),
    Ideal(..),
    destroyIdeal,

    -- * Ideal Monad Coproduct
    (:+)(..),
    inject1,
    inject2,
    (||||),

    -- * Mutual recursion for Ideal monad coproducts
    Mutual (..),

    -- * Relation between @MonadIdeal@, @Bind@, and @MonadIsolate@
    -- 
    -- $relation_to_bind_and_isolate
  )
where

import Prelude
import Data.Bifunctor ( Bifunctor(..) )
import Data.Bitraversable (bitraverse)
import Control.Arrow ((|||))

import Control.Functor.Internal.Mutual
import Data.Functor.Bind (Bind (..), Apply (..), apDefault)
import Control.Applicative (WrappedMonad (..))

newtype Ideal f a = Ideal { runIdeal :: Either a (f a) }
  deriving (Show, Read, Eq, Ord)
instance (Functor g) => Functor (Ideal g) where
  fmap f = Ideal . bimap f (fmap f) . runIdeal

instance (Foldable g) => Foldable (Ideal g) where
  foldMap f = either f (foldMap f) . runIdeal

instance (Traversable g) => Traversable (Ideal g) where
  traverse f = fmap Ideal . bitraverse f (traverse f) . runIdeal

-- | @m@ is the "Ideal part" of Ideal monad @Ideal m@.
--
-- ==== Laws
--
-- - (todo) @'Ideal' m@ is a lawful monad
-- - (todo) @('>>-') === bindDefault@
class (Bind m) => MonadIdeal m where
  idealBind :: m a -> (a -> Ideal m b) -> m b

infixl 1 `idealBind`

-- | 'MonadIdeal' implies 'Bind'
bindDefault :: MonadIdeal m => m a -> (a -> m b) -> m b
bindDefault ma k = ma `idealBind` Ideal . Right . k

idealize :: (MonadIdeal m) => m (Ideal m a) -> m a
idealize = (`idealBind` id)

-- | @Ideal ((,) s) ~ (,) (Maybe s)@
instance (Semigroup s) => MonadIdeal ((,) s) where
  idealBind (s1, a) k = case runIdeal (k a) of
    Left b -> (s1, b)
    Right (s2, b) -> (s1 <> s2, b)

-- | Any @Monad@ can be an Ideal of @Ideal m@
instance (Monad m) => MonadIdeal (WrappedMonad m) where
  idealBind (WrapMonad ma) k = WrapMonad $ ma >>= either pure unwrapMonad . runIdeal . k

instance (Apply m) => Apply (Ideal m) where
  fx <.> fy = case runIdeal fx of
    Left x -> x <$> fy
    Right mx -> case runIdeal fy of
      Left y   -> Ideal . Right $ ($ y) <$> mx
      Right my -> Ideal . Right $ mx <.> my
  
  fx .> fy = case runIdeal fx of
    Left _ -> fy
    Right mx -> case runIdeal fy of
      Left y -> Ideal . Right $ y <$ mx
      Right my -> Ideal . Right $ mx .> my

instance (Apply m) => Applicative (Ideal m) where
  pure = Ideal . Left
  (<*>) = (<.>)
  (*>) = (.>)

instance (MonadIdeal m) => Bind (Ideal m) where
  m >>- f = (id ||| Ideal . Right . idealize) . runIdeal $ fmap f m

instance (MonadIdeal m) => Monad (Ideal m) where
  (>>=) = (>>-)

destroyIdeal :: (m a -> a) -> Ideal m a -> a
destroyIdeal phi = (id ||| phi) . runIdeal

-- | Coproduct of 'MonadIdeal'
newtype (:+) m n a = IdealCoproduct { runIdealCoproduct :: Either (Mutual Either m n a) (Mutual Either n m a) }

inject1 :: (Functor m) => m a -> (m :+ n) a
inject1 = IdealCoproduct . Left . Mutual . fmap Left

inject2 :: (Functor n) => n a -> (m :+ n) a
inject2 = IdealCoproduct . Right . Mutual . fmap Left

instance (Functor m, Functor n) => Functor (m :+ n) where
  fmap f = IdealCoproduct . bimap (fmap f) (fmap f) . runIdealCoproduct

instance (MonadIdeal m, MonadIdeal n) => Apply (m :+ n) where
  (<.>) = apDefault

instance (MonadIdeal m, MonadIdeal n) => Bind (m :+ n) where
  (>>-) = bindDefault

instance (MonadIdeal m, MonadIdeal n) => MonadIdeal (m :+ n) where
  idealBind mutual k = IdealCoproduct $ case runIdealCoproduct mutual of
    Left mn -> Left $ bindMutual1 mn k
    Right nm -> Right $ bindMutual2 nm k

bindMutual1 :: (MonadIdeal m, MonadIdeal n) => Mutual Either m n a -> (a -> Ideal (m :+ n) b) -> Mutual Either m n b
bindMutual1 (Mutual mn) k =
  Mutual $
    mn `idealBind` \next ->
      case next of
        Left a -> case runIdeal (k a) of
          Left b -> pure (Left b)
          Right (IdealCoproduct (Left mn')) -> Ideal . Right $ runMutual mn'
          Right (IdealCoproduct (Right nm')) -> pure (Right nm')
        Right nm -> pure . Right $ bindMutual2 nm k

bindMutual2 :: (MonadIdeal m, MonadIdeal n) => Mutual Either m n a -> (a -> Ideal (n :+ m) b) -> Mutual Either m n b
bindMutual2 (Mutual mn) k =
  Mutual $
    mn `idealBind` \next ->
      case next of
        Left a -> case runIdeal (k a) of
          Left b -> pure (Left b)
          Right (IdealCoproduct (Left nm')) -> pure (Right nm')
          Right (IdealCoproduct (Right mn')) -> Ideal . Right $ runMutual mn'
        Right nm -> pure . Right $ bindMutual1 nm k

(||||) :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> (m :+ n) b -> t b
mt |||| nt = either (foldMutual mt nt) (foldMutual nt mt) . runIdealCoproduct

foldMutual :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> Mutual Either m n b -> t b
foldMutual mt nt (Mutual mn) = mt mn `idealBind` (Ideal . second (foldMutual nt mt))


{- $relation_to_bind_and_isolate

@MonadIdeal@ is a requirement stronger than both of 'Bind' and 'Control.Monad.Isolate.MonadIsolate'.
In fact, these implications hold.

- @MonadIdeal m@ implies @Bind m@
- @MonadIdeal m@ implies @MonadIsolate m (Ideal m)@

These implications are _strict_ and neither of three classes can be
replaced with other two.

- 'Data.List.NotOne.NotOne' is both @Bind@ and @MonadIsolate@, but not @MonadIdeal@.

- @NullBind c@ is @Bind@ but can't be a part of @MonadIsolate@.

@
data Nullify a = Null | NonNull a

newtype NullBind c a = NullBind (Nullify c)
instance Bind (NullBind c a) where
  _ >>- _ = NullBind Null
@

- @OddPart@ is @MonadIsolate@ with @Parity@ monad, but not @Bind@ in a compatible way.

@
data Parity a = Even a | Odd a

instance Monad Parity where
  return = Even
  Even a >>= k = k a
  Odd a >>= k = case k a of { Even b -> Odd b; Odd b -> Even b }

newtype OddPart a = OddPart a

instance MonadIsolate OddPart Parity where
  isolatePure ma = case ma of { Even a -> Left a; Odd a -> Right (OddPart a) }
  injectImpure (OddPart a) = Odd a
@

-}