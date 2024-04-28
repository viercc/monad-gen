# monad-ideals: Ideal Monads and coproduct of Monads

Revives `Control.Monad.Ideal` from old versions of [category-extras](https://hackage.haskell.org/package/category-extras-0.53.25).

## Ideal Monads

Ideal monads[^1] are certain kind of monads. Informally, an ideal monad `M`
is a `Monad` which can be written as a disjoint union of "pure" value and "impure" value,
and its `join` operation on "impure" values never produces "pure" values.

[^1]: N. Ghani and T. Uustalu, [“Coproducts of ideal monads,”](http://www.numdam.org/article/ITA_2004__38_4_321_0.pdf) Theoret. Inform. and Appl., vol. 38, pp. 321–342, 2004.

```haskell
data M a = Pure a | Impure (...)

pure :: a -> M a
pure = Pure

join :: M (M a) -> M a
join (Pure ma) = ma
join (Impure ...) = Impure (...)
  -- Impure values of @M a@ never becomes pure again 
```

Formally, an ideal monad `m` is a `Monad` equipped with 

- `Functor m₀`, called the ideal part of `m`
- Natural isomorphism `iso :: ∀a. Either a (m₀ a) -> m a` (and its inverse `iso⁻¹ :: ∀a. m a -> Either a (m₀ a)`)
- Natural transformation `idealize :: ∀a. m₀ (m a) -> m₀ a`

satisfying these two properties.

- `iso . Left === pure :: ∀a. a -> m a`
- `either id (iso . Right . idealize) . iso⁻¹ === join :: m (m a) -> m a`

This package provides `MonadIdeal`, a type class to represent ideal monads in terms of
its ideal part `m₀` (, instead of a subclass of `Monad` to represent ideal monad itself.)

```haskell
class (Isolated m0, Bind m0) => MonadIdeal m0 where
  idealBind :: m0 a -> (a -> Ideal m0 b) -> m0 b

type Ideal m0 a

-- | Constructor of @Ideal@
ideal :: Either a (m0 a) -> Ideal m0 a

-- | Deconstructor of @Ideal@
runIdeal :: Ideal m0 a -> Either a (m0 a)
```

Here, `Ideal m0` corresponds to the ideal monad which would have `m0` as its ideal part.

## `Isolated` class

There is a generalization to ideal monads which is almost ideal monads
but lacks a condition that says "an impure value does not become a pure value by `join`."

A monad `m` in this class has natural isomorphism `Either a (m₀ a) -> m a` with some functor `m₀`, and
`pure` is the part of `m` which is not `m₀`.

- `Functor m₀`, called the impure part of `m`
- Natural isomorphism `iso :: ∀a. Either a (m₀ a) -> m a` (and its inverse `iso⁻¹ :: ∀a. m a -> Either a (m₀ a)`)
- `iso . Left === pure :: ∀a. a -> m a`

Combined with the monad laws of `m`, `join :: ∀a. m (m a) -> m a` must be equal to the following natural transformation
with some `impureJoin`.

```haskell
join :: ∀a. m (m a) -> m a
join mma = case iso⁻¹ mma of
  Left ma -> ma
  Right m₀ma -> impureJoin m₀ma
  where
    impureJoin :: ∀a. m₀ (m a) -> m a
```

The `Isolated` class is a type class for a functor which can be thought of as an
impure part of some monad.

```haskell
newtype Unite f a = Unite { runUnite :: Either a (f a) }

class Functor m0 => Isolated m0 where
  impureBind :: m0 a -> (a -> Unite m0 b) -> Unite m0 b
```

## Coproduct of monads

Coproduct `m ⊕ n` of two monads[^2] `m, n` is the (category-theoretic) coproduct in the category of monad
and [monad morphisms](https://hackage.haskell.org/package/mmorph-1.2.0/docs/Control-Monad-Morph.html). [^3]

In basic terms, `m ⊕ n` is a monad with the following functions and properties.

- Monad morphism `inject1 :: ∀a. m a -> (m ⊕ n) a`
- Monad morphism `inject2 :: ∀a. n a -> (m ⊕ n) a`
- Function `eitherMonad` which takes two monad morphisms and return a monad morphism.

  ```
  eitherMonad :: (∀a. m a -> t a) -> (∀a. n a -> t a) -> (∀a. (m ⊕ n) a -> t a)
  ```

- Given arbitrary monads `m, n, t` and monad morphisms `f1 :: ∀a. m a -> t a` and `f2 :: ∀a. n a -> t a`,

  - `eitherMonad f1 f2 . inject1 = f1`
  - `eitherMonad f1 f2 . inject2 = f2`
  - Any monad morphism `f :: ∀a. (m ⊕ n) a -> t a` equals to `eitherMonad f1 f2` for some unique `f1, f2`.
    Or, equvalently, `f = eitherMonad (f . inject1) (f . inject2)`.

Coproduct of two monads does not always exist, but for ideal monads or monads with `Isolated` impure parts,
their coproducts exist. This package provides a type constructor `(:+)` below.

```haskell
-- Control.Monad.Coproduct
data (:+) (m :: Type -> Type) (n :: Type -> Type) (a :: Type)
```

Using this type constructor, coproduct of monad can be constructed in two ways.

- If `m0, n0` are `Isolated` i.e. the impure part of monads `Unite m0, Unite n0` respectively,
  `m0 :+ n0` is also `Isolated` and `Unite (m0 :+ n0)` is the coproduct of monads `Unite m0 ⊕ Unite n0`.

- If `m0, n0` are `MonadIdeal` i.e. the ideal part of ideal monads `Ideal m0, Ideal n0` respectively,
  `m0 :+ n0` is also `MonadIdeal` and `Ideal (m0 :+ n0)` is the coproduct of monads `Ideal m0 ⊕ Ideal n0`.

[^2]: Jiří Adámek, Nathan Bowler, Paul B. Levy and Stefan Milius, ["Coproducts of Monads on Set."](https://arxiv.org/abs/1409.3804) (https://doi.org/10.48550/arXiv.1409.3804)

[^3]: To name the same concept to monad morphism, the term "monad transformation" is used in `transformers` package ([Control.Monad.Trans.Class](https://hackage.haskell.org/package/transformers-0.6.0.3/docs/Control-Monad-Trans-Class.html#t:MonadTrans).)

## Duals

This package also provides the duals of ideal monads and coproducts of them: _Coideal comonads_ and _products_ of them.