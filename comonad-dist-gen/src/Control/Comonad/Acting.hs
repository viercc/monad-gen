{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Comonad.Acting
  ( -- * Acting comonad
    type Acting,
    pattern Acting,
    locate,
    direct,

    -- * Acting comonad transformer
    ActingT (..),
    trunc,

    -- * Isomorphism to @Store@
    toStore,
    fromStore,
    toStoreG,
    fromStoreG
  )
where

import Control.Comonad
import Control.Comonad.Hoist.Class (ComonadHoist (..))
import Control.Comonad.Store (Store, peek, pos, store)
import Control.Comonad.Trans.Class (ComonadTrans (..))
import Data.Monoid.Action (Action(..), Torsor(..))
import Data.Functor.Identity
import Data.Group (Group (..))

newtype ActingT s x w a = ActingT {runActingT :: w (x, s -> a)}
  deriving (Functor)

type Acting s x = ActingT s x Identity

pattern Acting :: x -> (s -> a) -> Acting s x a
pattern Acting x f = ActingT (Identity (x, f))

{-# COMPLETE Acting #-}

-- | @locate@ is @Control.Comonad.Store.'pos'@ equivalent for @Acting(T)@
locate :: (Comonad w) => ActingT s x w a -> x
locate = fst . extract . runActingT

-- | @direct@ is @Control.Comonad.Store.'peek'@ equivalent for @Acting(T)@
direct :: (Comonad w) => s -> ActingT s x w a -> a
direct s = ($ s) . snd . extract . runActingT

-- | Truncates "Comonad transformer stack" by erasing
--   any inner comonad @w@ to @Identity@.
--
-- > trunc :: EnvT e w a -> Env e a
-- > trunc :: StoreT s w a -> Store s a
-- > trunc :: ActingT s x w a -> Acting s x a
trunc :: (ComonadHoist t, Comonad w) => t w a -> t Identity a
trunc = cohoist (Identity . extract)

instance (Monoid s, Action s x, Comonad w) => Comonad (ActingT s x w) where
  extract = extractA . extract . runActingT
    where

  duplicate = fmap ActingT . ActingT . fmap dist . duplicate . fmap duplicateA . runActingT
    where
      dist :: forall a. w (x, s -> a) -> (x, s -> w a)
      dist w = (x0, \s -> peek' s <$> w)
        where
          x0 = fst (extract w)
          peek' s (_, f) = f s

instance ComonadHoist (ActingT s x) where
  cohoist phi = ActingT . phi . runActingT

instance (Monoid s) => ComonadTrans (ActingT s x) where
  lower = fmap extractA . runActingT

-- Comonad structure of "bare" Acting x s
extractA :: forall x s a. (Monoid s) => (x, s -> a) -> a
extractA (_, f) = f mempty

duplicateA :: forall x s a. (Semigroup s, Action s x) => (x, s -> a) -> (x, s -> (x, s -> a))
duplicateA (x, f) = (x, \s -> (s `act` x, f . (<> s)))

{-

Comonad laws for Acting

  mapA g (x,f) = (x, \s -> g (f s))
  extractA (_,f) = f mempty
  duplicateA (x,f) = (x, \s -> (s • x, f . (<> s)))

==== left unit ====

(extractA . duplicateA) (x,f)
 = extractA (x, \s -> (s • x, f . (<> s)))
 = (mempty • x, f . (<> mempty))
 = (x, f)

==== right unit ====

(mapA extractA . duplicateA) (x,f)
 = mapA extractA (x, \s -> (s • x, f . (<> s)))
 = (x, \s -> extractA (s • x, f . (<> s)))
 = (x, \s -> f (mempty <> s))
 = (x, f)

==== coassoc ====

(duplicateA . duplicateA) (x,f)
 = duplicateA (x, \s -> (s • x, f . (<> s)))
 = (x, \s1 ->
    (s1 • x, \s2 ->
      (\s -> (s • x, f . (<> s))(s2 <> s1))
    )
   )
 = (x, \s1 ->
    (s1  •  x, \s2 ->
      ((s2 <> s1) • x, f . (<> (s2 <> s1))
    )
   )
 = (x, \s1 ->
    (s1 • x, \s2 ->
      (s2 • s1 • x, \s3 -> f (s3 <> s2 <> s1)
    )
   )

(mapA duplicateA . duplicateA) (x,f)
 = mapA duplicateA (x, \s1 -> (s1 • x, f . (<> s1)))
 = (x, \s1 -> duplicateA (s1 • x, f . (<> s1)))
 = (x, \s1 ->
    (s1 • x, \s2 ->
      (s2 • s1 • x, f . (<> s1) . (<> s2)
    )
   )
 = (x, \s1 ->
    (s1 • x, \s2 ->
      (s2 • s1 • x, \s3 -> f (s3 <> s2 <> s1)
    )
   )

-}

-- | @Acting g x@ is isomorphic to @Store x@ when @x@ is @g@-@Torsor@
toStore :: (Torsor g x) => Acting g x a -> Store x a
toStore (Acting x0 f) = store' x0 (\x1 -> f (x1 `difference` x0))

fromStore :: (Action g x) => Store x a -> Acting g x a
fromStore w = Acting x0 (\g -> f (g `act` x0))
  where
    x0 = pos w
    f x1 = peek x1 w

store' :: x -> (x -> a) -> Store x a
store' = flip store

{-

==== comonad morphism ====
extract (toStore (Acting x0 f))
 = extract $ store' x0 $ \x1 -> f (x1 <-- x0)
 = f (x0 <-- x0)
 = f mempty
 = extract (Acting x0 f)

duplicate (toStore (Acting x0 f))
 = duplicate $ store' x0 $ \x1 -> f (x1 <-- x0)
 = store' x0 $ \x1 -> store' x1 $ \x2 -> f (x2 <-- x0)

(fmap toStore . toStore . duplicate) (Acting x0 f)
 = (fmap toStore . toStore) $ Acting x0 $ \g -> Acting (g • x0) (f . (<> g))
 = fmap toStore $ store' x0 $ \x1 -> Acting ((x1 <-- x0) • x0) (f . (<> (x1 <-- x0)))
 = fmap toStore $ store' x0 $ \x1 -> Acting x1 (f . (<> (x1 <-- x0)))
 = store' x0 $ \x1 -> toStore $ Acting x1 (f . (<> (x1 <-- x0)))
 = store' x0 $ \x1 -> store' x1 $ \x2 -> f . (<> (x1 <-- x0)) $ (x2 <-- x1)
 = store' x0 $ \x1 -> store' x1 $ \x2 -> f ((x2 <-- x1) <> (x1 <-- x0))
 = store' x0 $ \x1 -> store' x1 $ \x2 -> f (x2 <-- x0)

==== inverse ===

fromStore (toStore (Acting x0 f))
 = fromStore (store' x0 $ \x1 -> f (x1 <-- x0))
 = Acting x0 (\g -> f ((g • x0) <-- x0))
     -- by Torsor law
 = Acting x0 (\g -> f g)
 = Acting x0 f

toStore (fromStore (store' x0 f))
 = toStore (Acting x0 (\g -> f (g • x0)))
 = store' x0 $ \x1 -> f ((x1 <-- x0) • x0)
 = store' x0 $ \x1 -> f x1
 = store' x0 f

-}

-- | Same as 'toStore' but using the action of group @g@ on itself: @act = (<>)@
toStoreG :: (Group g) => Acting g g a -> Store g a
toStoreG (Acting g0 f) = store' g0 (\g1 -> f (g1 ~~ g0))

-- | Same as 'fromStore' but using the action of group @g@ on itself: @act = (<>)@
fromStoreG :: (Semigroup g) => Store g a -> Acting g g a
fromStoreG w = Acting g0 (\g -> f (g <> g0))
  where
    g0 = pos w
    f g1 = peek g1 w
