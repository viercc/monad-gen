{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}

module ModelFinder.Dependent.Expr(
  -- * Expression type
  Expr(..),
  call,
  lift0, lift1, lift2, lift3,

  getDemands,
  evaluate,
  evaluateReq,
  reduce,

  -- * Equational properties
  Property,
  equals, (===), evaluatesTo, equalsToFun, satisfies,
  getDemandsProperty,
  reduceProperty, reducePropertyWith,
  evaluateProperty, evaluatePropertyWith,

  SimpleProp(..),
  reduceSimpleProp,
  reduceSimplePropWith,
  evaluateSimpleProp,
  evaluateSimplePropWith,

  -- * Aux types
  IsChanged(..)
) where

import Data.Constraint.Extras (Has (..))
import Data.Some (Some (..))

-- | Expression with unknown functions.
--
-- (Not actually a @Monad@ or even @Functor@,
-- but "morally" it is.)
data Expr f a where
  Pure :: a -> Expr f a
  Call :: f v -> Expr f v
  Combine :: Expr f a -> Expr f b -> Expr f (a,b)
  Bind :: Expr f a -> (a -> Expr f b) -> Expr f b

instance Functor (Expr f) where
  fmap f (Pure a) = Pure (f a)
  fmap f ma = Bind ma (Pure . f)

instance Applicative (Expr f) where
  pure = Pure

  liftA2 f ex ey = Bind (Combine ex ey) (Pure . uncurry f)

instance Monad (Expr f) where
  Pure x >>= k = k x
  mx >>= k = Bind mx k

-- | Transform an @Expr@ so that if it ends with @Call fx@,
--   replaces it with @Pure@. Distinguished between the case ending in @Pure@
--   using @Either@.
exposeLeaf :: Expr f x -> Expr f (Either (f x) x)
exposeLeaf (Pure x) = Pure (Right x)
exposeLeaf (Call fx) = Pure (Left fx)
exposeLeaf ex@(Combine _ _) = Bind ex (Pure . Right)
exposeLeaf (Bind ex k) = Bind ex (exposeLeaf . k)

-- | View of the Expr.
data Expr' f a where
  Pure' :: a -> Expr' f a
  Demand' :: Requests f v -> (v -> Expr f a) -> Expr' f a

data Requests f v where
  Request :: !(f v) -> Requests f v
  RequestBoth :: !(Requests f v1) -> !(Requests f v2) -> Requests f (v1, v2)

view :: Expr f a -> Expr' f a
view (Pure a) = Pure' a
view (Call fx) = Demand' (Request fx) Pure
view (Combine ma mb) = case (view ma, view mb) of
  (Pure' a, Pure' b) -> Pure' (a,b)
  (Pure' a, Demand' reqB contB) -> Demand' reqB (\vb -> Pure a `Combine` contB vb)
  (Demand' reqA contA, Pure' b) -> Demand' reqA (\va -> contA va `Combine` Pure b)
  (Demand' reqA contA, Demand' reqB contB) -> Demand' (RequestBoth reqA reqB) (\(va, vb) -> Combine (contA va) (contB vb))
view (Bind ma cont) = case view ma of
  Pure' a -> view (cont a)
  Demand' reqA contA -> Demand' reqA (\a -> Bind (contA a) cont)

call :: f x -> Expr f x
call = Call

lift0 :: f x -> Expr f x
lift0 = Call

lift1 :: (x -> f y) -> Expr f x -> Expr f y
lift1 con ex = ex >>= \x -> Call (con x)

lift2 :: (x1 -> x2 -> f y) -> Expr f x1 -> Expr f x2 -> Expr f y
lift2 con ex1 ex2 = Bind (Combine ex1 ex2) $ \(x1,x2) -> Call (con x1 x2)

lift3 :: (x1 -> x2 -> x3 -> f y) -> Expr f x1 -> Expr f x2 -> Expr f x3 -> Expr f y
lift3 con ex1 ex2 ex3 = Bind (Combine ex1 (Combine ex2 ex3)) $ \(x1,(x2,x3)) -> Call (con x1 x2 x3)

-- | Get a list of unknonws required to progress evaluation
getDemands :: Expr f a -> [ Some f ]
getDemands e = case view e of
  Pure' _ -> []
  Demand' reqs _ -> reqToList reqs

reqToList :: Requests f xs -> [ Some f ]
reqToList = ($ []) . go
  where
    go :: forall f r. Requests f r -> [ Some f ] -> [ Some f ]
    go (Request fx) = (Some fx :)
    go (RequestBoth r1 r2) = go r1 . go r2

-- | Evaluate an expression with monadic effect.
evaluate :: forall f m a. (Monad m) => (forall x. f x -> m x) -> Expr f a -> m a
evaluate ev = go
  where
    go :: forall r. Expr f r -> m r
    go (Pure a) = pure a
    go (Call fx) = ev fx
    go (Combine ma mb) = liftA2 (,) (go ma) (go mb)
    go (Bind ma k) = go ma >>= go . k

-- | Evaluate requests
evaluateReq :: forall f m a. (Applicative m) => (forall x. f x -> m x) -> Requests f a -> m a
evaluateReq ev = go
  where
    go :: forall r. Requests f r -> m r
    go (Request fx) = ev fx
    go (RequestBoth r1 r2) = (,) <$> go r1 <*> go r2

-- | Reduce expression as much as you can.
reduce :: forall f a. (forall x. f x -> Maybe x) -> Expr f a -> (IsChanged, Expr f a)
reduce ev = go
  where
    combine :: forall x y. Expr f x -> Expr f y -> Expr f (x,y)
    combine (Pure x) (Pure y) = Pure (x,y)
    combine (Pure x) (Bind my ky) = Bind my $ \y -> combine (Pure x) (ky y)
    combine (Bind mx kx) (Pure y) = Bind mx $ \x -> combine (kx x) (Pure y)
    combine mx my = Combine mx my

    go :: forall r. Expr f r -> (IsChanged, Expr f r)
    go ma = case ma of
      Pure _ -> (NoChange, ma)
      Call fx -> maybe (NoChange, ma) ((Changed,) . pure) (ev fx)
      Combine ma1 ma2 -> combine <$> go ma1 <*> go ma2
      Bind mb k -> case go mb of
        (changed, mb') -> case mb' of
          Pure b -> (Changed, snd $ go (k b))
          _ -> (changed, Bind mb' k)

-- * Equational properties

data SimpleProp f where
  PropFail :: SimpleProp f
  PropSuccess :: SimpleProp f
  -- | Determines an unknown to a value
  PropDef :: !(f x) -> !x -> SimpleProp f
  -- | Two unknowns are equal
  PropSimpleEq :: !(f x) -> !(f x) -> SimpleProp f
  -- | Impose restriction on an unknown value
  PropSimplePred :: !(f x) -> (x -> Bool) -> SimpleProp f

boolProp :: Bool -> SimpleProp f
boolProp b = if b then PropSuccess else PropFail

propEq :: Eq x => x -> x -> SimpleProp f
propEq x y = boolProp (x == y)

-- | Expressions written in Props
type Property f = Expr f (SimpleProp f)

infix 1 `equals`
infix 1 ===

equals, (===) :: Eq x => Expr f x -> Expr f x -> Property f
equals ex ey = liftA2 f (exposeLeaf ex) (exposeLeaf ey)
  where
    f (Left fx) (Left fy) = PropSimpleEq fx fy
    f (Left fx) (Right y) = PropDef fx y
    f (Right x) (Left fy) = PropDef fy x
    f (Right x) (Right y) = boolProp $ x == y

(===) = equals

infix 1 `evaluatesTo`

evaluatesTo :: Eq x => Expr f x -> x -> Property f
evaluatesTo ex y = either (flip PropDef y) (propEq y) <$> exposeLeaf ex

infix 1 `equalsToFun`

equalsToFun :: Expr f x -> f x -> Property f
equalsToFun ex fy = either (PropSimpleEq fy) (PropDef fy) <$> exposeLeaf ex

infix 1 `satisfies`

satisfies :: Expr f x -> (x -> Bool) -> Property f
satisfies ex p = either (flip PropSimplePred p) (boolProp . p) <$> exposeLeaf ex

reducePropertyWith :: forall f. (forall x. f x -> x -> x -> Bool) -> (forall x. f x -> Maybe x) -> Property f -> (IsChanged, Property f)
reducePropertyWith getEq ev prop = case reduce ev prop of
  (changed, prop') -> case prop' of
    Pure p -> case reduceSimplePropWith getEq ev p of
      (changedSimpl, p') -> (changed <> changedSimpl, Pure p')
    _ -> (changed, prop')

reduceProperty :: forall f. (Has Eq f) => (forall x. f x -> Maybe x) -> Property f -> (IsChanged, Property f)
reduceProperty = reducePropertyWith hasEq

hasEq :: Has Eq f => f x -> x -> x -> Bool
hasEq fx = has @Eq fx (==)

reduceSimpleProp :: forall f. (Has Eq f) => (forall x. f x -> Maybe x) -> SimpleProp f -> (IsChanged, SimpleProp f)
reduceSimpleProp = reduceSimplePropWith hasEq

reduceSimplePropWith :: forall f. (forall x. f x -> x -> x -> Bool) -> (forall x. f x -> Maybe x) -> SimpleProp f -> (IsChanged, SimpleProp f)
reduceSimplePropWith getEq ev p =
  case p of
    PropFail -> (NoChange, PropFail)
    PropSuccess -> (NoChange, PropSuccess)
    PropDef fx y -> case ev fx of
      Nothing -> (NoChange, p)
      Just x -> (Changed, boolProp (getEq fx x y))
    PropSimpleEq fx fy -> case (ev fx, ev fy) of
      (Nothing, Nothing) -> (NoChange, p)
      (Just x,  Nothing) -> (Changed, PropDef fy x)
      (Nothing, Just y)  -> (Changed, PropDef fx y)
      (Just x, Just y) -> (Changed, boolProp (getEq fx x y))
    PropSimplePred fx cond -> case ev fx of
      Nothing -> (NoChange, p)
      Just x -> (Changed, boolProp (cond x))

evaluatePropertyWith :: forall f m. (Monad m)
  => (forall x. f x -> x -> x -> Bool)
  -> (forall x. f x -> m x) -> Property f -> m Bool
evaluatePropertyWith getEq ev property =
  evaluate ev property >>= evaluateSimplePropWith getEq ev

evaluateSimplePropWith :: forall f m. (Applicative m)
  => (forall x. f x -> x -> x -> Bool)
  -> (forall x. f x -> m x) -> SimpleProp f -> m Bool
evaluateSimplePropWith getEq ev p =
  case p of
    PropFail -> pure False
    PropSuccess -> pure True
    PropDef fx y -> getEq fx y <$> ev fx
    PropSimpleEq fx fy -> getEq fx <$> ev fx <*> ev fy
    PropSimplePred fx cond -> cond <$> ev fx

evaluateProperty :: forall f m. (Has Eq f, Monad m) => (forall x. f x -> m x) -> Property f -> m Bool
evaluateProperty = evaluatePropertyWith hasEq

evaluateSimpleProp :: forall f m. (Has Eq f, Applicative m) => (forall x. f x -> m x) -> SimpleProp f -> m Bool
evaluateSimpleProp = evaluateSimplePropWith hasEq

getDemandsProperty :: forall f. Property f -> [ Some f ]
getDemandsProperty p = case p of
  Pure sp -> getDemandsSimpleProp sp
  _ -> getDemands p

getDemandsSimpleProp :: forall f. SimpleProp f -> [ Some f ]
getDemandsSimpleProp simp = case simp of
    PropFail -> []
    PropSuccess -> []
    PropDef fx _ -> [ Some fx ]
    PropSimpleEq fx fy -> [ Some fx, Some fy ]
    PropSimplePred fx _ -> [ Some fx ]

-- | Common type to express "is it changed?" flag
data IsChanged = NoChange | Changed
  deriving stock (Show, Eq)

instance Semigroup IsChanged where
  NoChange <> y = y
  Changed <> _ = Changed

instance Monoid IsChanged where
  mempty = NoChange