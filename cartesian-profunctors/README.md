# cartesian-profunctors

This package provides three major type classes. Two of them are defined in [Data.Profunctor.Cartesian](src/Data/Profunctor/Cartesian.hs), and the remaining one is defined in [Data.PTraversable](src/Data/PTraversable.hs).

## Data.Profunctor.Cartesian

```haskell
-- Defined in Data.Profunctor.Cartesian

class Profunctor p => Cartesian p where
  proUnit :: p a ()
  (***) :: p a b -> p a' b' -> p (a,a') (b,b')

class Profunctor p => Cocartesian p where
  proEmpty :: p Void b
  (+++) :: p a b -> p a' b' -> p (Either a a') (Either b b')
```

These classes are subclasses of [Profunctor](http://hackage.haskell.org/package/profunctors-5.5/docs/Data-Profunctor.html). For someone not familiar with Profunctors, there is a good articles online: [I love profunctors. They're so easy. - School of Haskell](https://www.schoolofhaskell.com/school/to-infinity-and-beyond/pick-of-the-week/profunctors#example--containers-with-keys).

They are also similar to [Arrow and ArrowChoice](http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Arrow.html), but they have important differences.

* Arrow and ArrowChoice are subclasses of [Category](http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Category.html#t:Category), so they have identity and compose each other.
* Arrows have `arr`, which lifts every Haskell function `a -> b` into an Arrow `p a b`.

To see the similarity and difference between Cartesian and Arrow, let's check every Arrow can be Profunctor and Cartesian.

```haskell
instance Arrow P

instance Profunctor P where
  dimap l r p = arr l >>> p >>> arr r
instance Cartesian P where
  proUnit = arr (const ())
  (***) = (Control.Arrow.***)
```

And every ArrowChoice can be Cocartesian.

```haskell
instance ArrowChoice P

instance Cocartesian P where
  proEmpty = arr absurd
  (+++) = (Control.Arrow.+++)
```

But it's not the case other way around. Being Cartesian or Cocartesian do not give you an ability to write:

* `id :: forall a. p a a`
* `(>>>) :: forall a b c. p a b -> p b c -> p a c`

Which Profunctos are instances of Cartesian/Cocartesian?
Luckily, most basic Profunctor '->' is Cartesian and Cocartesian.

```haskell
instance Cartesian (->) where
  proUnit = const ()
  p *** q = (Control.Arrow.***) p q
          = bimap p q
          = \(a,a') -> (p a, q a')

instance Cocartesian (->) where
  proEmpty = absurd
  p +++ q = (Control.Arrow.+++) p q
          = bimap p q
          = \e -> case e of
              Left a   -> Left (p a)
              Right a' -> Right (q a')
```

To put another example, [Star f](http://hackage.haskell.org/package/profunctors-5.5/docs/Data-Profunctor.html#t:Star) is a Category (and can be Arrow, ArrowChoice) only when `f` is a Monad.
But, being Cartesian and Cocartesian requires `f` only to be Applicative.

```haskell
newtype Star f a b = Star (a -> f b)

instance Applicative f => Cartesian (Star f) where
  proUnit :: Star f a ()
  proUnit = Star (const (pure ())

  (***) :: Star f a b -> Star f a' b' -> Star f (a,a') (b,b')
  Star p *** Star q = Star $ \(a,a') -> liftA2 (,) (p a) (q a')

instance Functor f => Cocartesian (Star f) where
  proEmpty :: Star f Void b
  proEmpty = Star absurd

  (+++) :: Star f a b -> Star f a' b' -> Star f (Either a a') (Either b b')
  Star p +++ Star q = Star $ either (fmap Left . p) (fmap Right . q)
```

## Data.PTraversable

Using Cartesian and Cocartesian, this package provides another type class, [PTraversable](src/Data/PTraversable.hs). <sup><a id="fn1a" href="#fn1">*1</a></sup>

```haskell
class (Traversable t) => PTraversable t where
  ptraverse :: (Cartesian p, Cocartesian p)
            => p a b -> p (t a) (t b)
```

`PTraversable` is really powerful. Putting previously found Cartesian & Cocartesian Profunctors to `p`, you can get various powers!

* Simply putting `p = (->)`, you get `(a -> b) -> t a -> t b`, which is `fmap`.
* Putting `p = Star f` for Applicative `f`, you get `Star f a b -> Star f (t a) (t b)`. By unwrapping `Star`, you get:

  ```haskell
  ptraverse :: (Applicative f) => (a -> f b) -> t a -> f (t b)
  ```

  `traverse`! This is the reason why I named this function `ptraverse`.

* Being able to `traverse` means it also enables Foldable methods.
* Outside of `traverse` family, `PTraversable t` also means `Eq a => Eq (t a)`.

  ```haskell
  -- Defined in Data.Functor.Contravariant (base)
  newtype Equivalence a = Equivalence { getEquivalence :: a -> a -> Bool }
  instance Contravariant Equivalence

  -- Defined in Data.Functor.Contravariant.Divisible (contravariant)
  instance Divisible Equivalence
  instance Decidable Equivalence
  
  -- Defined in Data.Bifunctor.Clown (bifunctors)
  newtype Clown f a b = Clown { runClown :: f a }

  instance Contravariant f => Profunctor (Clown f)
  instance Divisible f => Cartesian (Clown f)
  instance Decidable f => Cocartesian (Clown f)
  
  ptraverse :: Clown Equivalence a b -> Clown Equivalence (t a) (t b)
  --           (a -> a -> Bool) -> (t a -> t a -> Bool)
  
  eq1 :: (Eq a) => t a -> t a -> Bool
  eq1 = getEquivalence . runClown . ptraverse . Clown . Equivalence $ (==)

  -- Also `Ord a => Ord (t a)` can be defined in the similar manner.
  ```

Then how can I write the instance of `PTraversable`? `Maybe` can be a `PTraversable` by the following code:

```haskell
instance PTraversable Maybe where
  ptraverse :: (Cartesian p, Cocartesian p)
            => p a b -> p (Maybe a) (Maybe b)
  ptraverse p = dimap toEither fromEither $ proUnit +++ p
    where toEither :: Maybe a -> Either () a
          toEither = maybe (Left ()) Right
          fromEither :: Either () b -> Maybe b
          fromEither = either (const Nothing) Just
```

And for another simple Functor:

```haskell
data Two a = Two a a
  deriving (Functor, Foldable, Traversable)

instance PTraversable Two where
  ptraverse :: (Cartesian p, Cocartesian p)
            => p a b -> p (Two a) (Two b)
  ptraverse p = dimap (\Two a a' -> (a,a')) (\(a,a') -> Two a a') $ p *** p
```

(TODO: More careful and gentle explanation)

(TODO: Explain Generics)

## Further works

* Isn't there a work (libraries, papers) for these classes?
* What law should I put on?
  * I'm sure Monoid-like law for Cartesian and Cocartesian is necessary
  * Should (***) distribute over (+++)?
  * How PTraversable law should look like?
* Documentation
* Check performance

--------

<a id="fn1">This is a bit different to what the actual code are, to use  GeneralizedNewtypeDeriving and DerivingVia. But morally there's no difference.</a><a href="#fn1a">(back)</a>
