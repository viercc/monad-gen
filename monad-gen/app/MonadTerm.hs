{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
module MonadTerm where

import Data.Bifunctor (Bifunctor(..))

data Term f x = In (f x) | Join (Term f (Term f x))
   deriving (Functor, Foldable, Traversable)

deriving instance (forall a. Show a => Show (f a), Show x) => Show (Term f x)
deriving instance (forall a. Eq a => Eq (f a), Eq x) => Eq (Term f x)
deriving instance (forall a. Eq a => Eq (f a), forall a. Ord a => Ord (f a), Ord x) => Ord (Term f x)

getSingle :: Term f x -> Maybe (f x)
getSingle (In fx) = Just fx
getSingle _ = Nothing

getJoinSingles :: Traversable f => Term f x -> Maybe (f (f x))
getJoinSingles (Join (In ftx)) = traverse getSingle ftx
getJoinSingles _ = Nothing

data HasChange = HasChange | NoChanges
    deriving (Show, Eq)

instance Semigroup HasChange where
    HasChange <> _ = HasChange
    NoChanges <> y = y

instance Monoid HasChange where
    mempty = NoChanges

reduce :: forall f. (Traversable f) => (forall y. f (f y) -> Maybe (f y)) -> (forall x. Term f x -> (HasChange, Term f x))
reduce joinMaybe = go
  where
    go :: (Traversable f) => Term f x -> (HasChange, Term f x)
    go (In fx) = (NoChanges, In fx)
    go (Join (In ftx)) = case traverse go ftx of
        (changed, ftx') -> case traverse getSingle ftx' >>= joinMaybe of
            Nothing -> (changed, Join (In ftx'))
            Just fx -> (HasChange, In fx)
    go (Join (Join ttx)) = case go (Join ttx) of
        (HasChange, ttx') -> first (const HasChange) $ go (Join ttx')
        _ -> (NoChanges, Join (Join ttx))

getBlockers :: forall f r x. (Traversable f, Monoid r) => (forall z. f (f z) -> r) -> Term f x -> r
getBlockers _ (In _) = mempty
getBlockers f (Join (In ftx)) = case traverse getSingle ftx of
    Nothing -> foldMap (getBlockers f) ftx
    Just ffx -> f ffx
getBlockers f (Join (Join ttx)) = getBlockers f (Join ttx)

leftAssocTerm :: Functor f => f (f (f x)) -> Term f x
leftAssocTerm = Join . Join . In . fmap (In . fmap In)

rightAssocTerm :: Functor f => f (f (f x)) -> Term f x
rightAssocTerm = Join . fmap Join . In . fmap (In . fmap In)

data ReductionResult f x = Reduced (f x) (f x) | ReducedAlmost (f (f x)) (f x) | Unreduced (Term f x) (Term f x)

reduceEquation :: (Traversable f) => (forall z. f (f z) -> Maybe (f z)) -> (forall x. Term f x -> Term f x -> ReductionResult f x)
reduceEquation joinMaybe t1 t2 = case (t1', t2') of
    (In f1, In f2) -> Reduced f1 f2
    (In f1, Join (In ftx)) -> case traverse getSingle ftx of
        Nothing -> Unreduced t1' t2'
        Just ffx -> ReducedAlmost ffx f1
    (In _, _) -> Unreduced t1' t2'
    (Join (In ftx), In f2) -> case traverse getSingle ftx of
        Nothing -> Unreduced t1' t2'
        Just ffx -> ReducedAlmost ffx f2
    (_,_) -> Unreduced t1' t2'
    where
        (_, t1') = reduce joinMaybe t1
        (_, t2') = reduce joinMaybe t2