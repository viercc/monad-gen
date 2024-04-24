{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------------

----------------------------------------------------------------------------

-- |
-- Module      :  Control.Functor.Internal.Ideal
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Functor.Internal.Ideal
  ( -- * Common shape of (co)ideal
    Ap (..),

    -- * Ideal Monads
    MonadIdeal (..),
    Ideal,
    ideal, runIdeal,
    destroyIdeal,
    bindDefault,

    -- * Coideal Comonads
    ComonadCoideal (..),
    Coideal,
    coideal, runCoideal,
    buildCoideal,

    -- * Mutual recursion for (co)ideal (co)monad (co)products
    Mutual (..),
    Mutual' (..),

    -- * Coideal Comonad Product
    (:*),

    -- * Ideal Monad Coproduct
    (:+),
    inject1,
    inject2,
    (||||),
  )
where

import Prelude
import Data.Bifunctor
import Data.Bifoldable
import Control.Arrow ((&&&), (|||))
import Control.Comonad

import Control.Functor.Internal.Mutual
import Data.Functor.Bind (Bind (..), Apply (..), apDefault)
import Control.Applicative (WrappedMonad (..))

newtype Ap t f a = MkAp {runAp :: t a (f a)}

instance (Bifunctor t, Functor g) => Functor (Ap t g) where
  fmap f = MkAp . bimap f (fmap f) . runAp

instance (Bifoldable t, Foldable g) => Foldable (Ap t g) where
  foldMap f = bifoldMap f (foldMap f) . runAp

type Ideal = Ap Either

type Coideal = Ap (,)

ideal :: Either a (f a) -> Ideal f a
ideal = MkAp

coideal :: (a, f a) -> Coideal f a
coideal = MkAp

runIdeal :: Ideal f a -> Either a (f a)
runIdeal = runAp

runCoideal :: Coideal f a -> (a, f a)
runCoideal = runAp

-- | @m@ is the "ideal part" of ideal monad @Ideal m@.
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
bindDefault ma k = ma `idealBind` ideal . Right . k

idealize :: (MonadIdeal m) => m (Ideal m a) -> m a
idealize = (`idealBind` id)

-- | @Ideal ((,) s) ~ (,) (Maybe s)@
instance (Semigroup s) => MonadIdeal ((,) s) where
  idealBind (s1, a) k = case runIdeal (k a) of
    Left b -> (s1, b)
    Right (s2, b) -> (s1 <> s2, b)

-- | Any @Monad@ can be an ideal of @Ideal m@
instance (Monad m) => MonadIdeal (WrappedMonad m) where
  idealBind (WrapMonad ma) k = WrapMonad $ ma >>= either pure unwrapMonad . runIdeal . k

instance (Apply m) => Apply (Ideal m) where
  fx <.> fy = case runIdeal fx of
    Left x -> x <$> fy
    Right mx -> case runIdeal fy of
      Left y   -> ideal . Right $ ($ y) <$> mx
      Right my -> ideal . Right $ mx <.> my
  
  fx .> fy = case runIdeal fx of
    Left _ -> fy
    Right mx -> case runIdeal fy of
      Left y -> ideal . Right $ y <$ mx
      Right my -> ideal . Right $ mx .> my

instance (Apply m) => Applicative (Ideal m) where
  pure = ideal . Left
  (<*>) = (<.>)
  (*>) = (.>)

instance (MonadIdeal m) => Bind (Ideal m) where
  m >>- f = (id ||| ideal . Right . idealize) . runIdeal $ fmap f m

instance (MonadIdeal m) => Monad (Ideal m) where
  (>>=) = (>>-)

destroyIdeal :: (m a -> a) -> Ideal m a -> a
destroyIdeal phi = (id ||| phi) . runIdeal

class (Functor w) => ComonadCoideal w where
  coidealExtend :: (Coideal w a -> b) -> w a -> w b

coidealize :: (ComonadCoideal w) => w a -> w (Coideal w a)
coidealize = coidealExtend id

instance (ComonadCoideal w) => Comonad (Coideal w) where
  extract = fst . runCoideal
  extend f = fmap f . coideal . (id &&& coidealize . snd . runCoideal)

buildCoideal :: (a -> w a) -> a -> Coideal w a
buildCoideal phi = coideal . (id &&& phi)

-- instance ComonadCoideal (Fst k) where
-- coidealize = mkFst . runFst

-- * (Co)ideal (Co)products

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
          Right (IdealCoproduct (Left mn')) -> ideal . Right $ runMutual mn'
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
          Right (IdealCoproduct (Right mn')) -> ideal . Right $ runMutual mn'
        Right nm -> pure . Right $ bindMutual1 nm k

(||||) :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> (m :+ n) b -> t b
mt |||| nt = either (foldMutual mt nt) (foldMutual nt mt) . runIdealCoproduct

foldMutual :: (MonadIdeal t) => (forall a. m a -> t a) -> (forall a. n a -> t a) -> Mutual Either m n b -> t b
foldMutual mt nt (Mutual mn) = mt mn `idealBind` (ideal . fmap (foldMutual nt mt))

instance (ComonadCoideal w, ComonadCoideal v) => ComonadCoideal (w :* v) where
  coidealExtend k (Mutual' (wv, vw)) = Mutual' (extendMutual1 k wv, extendMutual2 k vw)

extendMutual1 ::
  (ComonadCoideal w, ComonadCoideal v) =>
  (Coideal (Mutual' (,) w v) a -> b) ->
  Mutual (,) w v a ->
  Mutual (,) w v b
extendMutual1 k (Mutual wv) =
  Mutual $ coidealExtend (\(MkAp ((a, vw), w')) -> (k (coideal (a, Mutual' (Mutual w', vw))), extendMutual2 k vw)) wv

extendMutual2 ::
  (ComonadCoideal w, ComonadCoideal v) =>
  (Coideal (Mutual' (,) v w) a -> b) ->
  Mutual (,) w v a ->
  Mutual (,) w v b
extendMutual2 k (Mutual wv) =
  Mutual $ coidealExtend (\(MkAp ((a, vw), w')) -> (k (coideal (a, Mutual' (vw, Mutual w'))), extendMutual1 k vw)) wv