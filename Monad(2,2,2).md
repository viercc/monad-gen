# Monad(2,2,2)

Source: https://github.com/viercc/monad-gen/blob/83eb84cc96ce798030ec9bed1dbe5beac12b2c28/monad-gen/output/Ugroups.txt

## Definition

```haskell
-- U a = a^2 + a^2 + a^2 = 3 * a^2
data U a = Ua a a | Ub a a | Uc a a
  deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic1)
deriving via (Generically1 U) instance PTraversable U
```

## Monoids on `Shape U`

```
Elements:
0 = Shape (Ua _ _)
1 = Shape (Ub _ _)
2 = Shape (Uc _ _)

Unit element: 0

M_1 = Monoid{
  Multiplication table: 
      | 0 1 2 
    --+-------
    0 | 0 1 2 
    1 | 1 0 2 
    2 | 2 2 2 
}
M_2 = Monoid{
  Multiplication table: 
      | 0 1 2 
    --+-------
    0 | 0 1 2 
    1 | 1 1 1 
    2 | 2 1 1 
}
M_3 = Monoid{
  Multiplication table: 
      | 0 1 2 
    --+-------
    0 | 0 1 2 
    1 | 1 1 1 
    2 | 2 1 2 
}
M_4 = Monoid{
  Multiplication table: 
      | 0 1 2 
    --+-------
    0 | 0 1 2 
    1 | 1 1 1 
    2 | 2 2 2 
}
M_5 = Monoid{
  Multiplication table: 
      | 0 1 2 
    --+-------
    0 | 0 1 2 
    1 | 1 1 2 
    2 | 2 1 2 
}
M_6 = Monoid{
  Multiplication table: 
      | 0 1 2 
    --+-------
    0 | 0 1 2 
    1 | 1 2 0 
    2 | 2 0 1 
}
M_7 = Monoid{
  Multiplication table: 
      | 0 1 2 
    --+-------
    0 | 0 1 2 
    1 | 1 1 2 
    2 | 2 2 1 
}
```

## Monads

Picked one from each isomorphism classes by hand

```
IsomorphismClass {
  Monad_1 = Monad{
    baseMonoid = M_1
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ua 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ua 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ua 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 1 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 1 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 1 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Uc 1 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Uc 1 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Uc 1 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Uc 1 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Uc 1 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Uc 1 3
  }
}
```
```
IsomorphismClass {
  Monad_2 = Monad{
    baseMonoid = M_1
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ua 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ua 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ua 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Uc 0 3
  }
}
```
```
IsomorphismClass {
  Monad_3 = Monad{
    baseMonoid = M_2
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Ub 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Ub 0 3
  }
}
```
```
IsomorphismClass {
  Monad_4 = Monad{
    baseMonoid = M_3
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Ub 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Uc 0 3
  }
}
```
```
IsomorphismClass {
  Monad_5 = Monad{
    baseMonoid = M_3
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 1 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 1 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 1 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ub 1 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ub 1 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ub 1 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Ub 1 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Ub 1 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Ub 1 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Uc 0 3
  }
}
```
```
IsomorphismClass {
  Monad_6 = Monad{
    baseMonoid = M_4
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 1 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 1 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 1 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ub 1 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ub 1 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ub 1 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Ub 1 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Ub 1 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Ub 1 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 1 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 1 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 1 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Uc 1 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Uc 1 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Uc 1 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Uc 1 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Uc 1 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Uc 1 3
  }
}
```
```
IsomorphismClass {
  Monad_7 = Monad{
    baseMonoid = M_4
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Ub 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Uc 0 3
  }
}
```
```
IsomorphismClass {
  Monad_8 = Monad{
    baseMonoid = M_5
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Uc 0 3
  }
}
```
```
IsomorphismClass {
  Monad_9 = Monad{
    baseMonoid = M_6
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Uc 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Uc 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Ua 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Ua 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Ua 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Ua 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Ua 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Ua 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Ub 0 3
  }
}
```
```
IsomorphismClass {
  Monad_10 = Monad{
    baseMonoid = M_7
    pure 0 = Ua 0 0
    join $ Ua (Ua 0 1) (Ua 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Ub 2 3) = Ua 0 3
    join $ Ua (Ua 0 1) (Uc 2 3) = Ua 0 3
    join $ Ua (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ua (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ua (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ua (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Ub (Ua 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ua 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ua 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Ub 2 3) = Ub 0 3
    join $ Ub (Ub 0 1) (Uc 2 3) = Ub 0 3
    join $ Ub (Uc 0 1) (Ua 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Ub 2 3) = Uc 0 3
    join $ Ub (Uc 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ua 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ua 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Ub 2 3) = Uc 0 3
    join $ Uc (Ub 0 1) (Uc 2 3) = Uc 0 3
    join $ Uc (Uc 0 1) (Ua 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Ub 2 3) = Ub 0 3
    join $ Uc (Uc 0 1) (Uc 2 3) = Ub 0 3
  }
}
```

## Description

| Name     | Base Monoid | Isomorphic to |
| -------- | -------- | -------- |
| `Monad_1` | `M1` | ? |
| `Monad_2` | `M1` | `Product (Writer M1) Identity` |
| `Monad_3` | `M2` | `Product (Writer M2) Identity` |
| `Monad_4` | `M3` | `Product (Writer M3) Identity` |
| `Monad_5` | `M3` | ? |
| `Monad_6` | `M4` | ? |
| `Monad_7` | `M4` | `Product (Writer M4) Identity` |
| `Monad_8` | `M5` | `Product (Writer M5) Identity` |
| `Monad_9` | `M6` | `Product (Writer M6) Identity` |
| `Monad_10` | `M7` | `Product (Writer M7) Identity` |

To see what's happening, I'm going to write down the unexplained monad instances, `Monad_1`, `Monad_5`, `Monad_6`, Using the alternative representation of `U`.

* `Monad_1` case

  ```haskell
  data M1 = A | B | C
  data U1 a = U1 M1 a a
  -- Ua = U1 A
  -- Ub = U1 B
  -- Uc = U1 C

  instance Semigroup M1 where
      C <> _ = C
      _ <> C = C
      A <> y = y
      x <> A = x
      B <> B = A
  instance Monoid M1 where
      mempty = A

  instance Monad U1 where
      pure x = U1 mempty x x
      join (U1 a (U1 b x1 y1) (U1 _ _ y2)) =
          let z1 = case a of
              A -> x1
              B -> x1
              C -> y1
              z2 = y2
          in U1 (a <> b) z1 z2
  ```


* `Monad_5` case

  ```haskell
  data M3 = A | B | C
      deriving (Eq, Ord)
  data U5 a = U5 M3 a a

  -- Note the renaming (a -> A, b -> C, c -> B)
  -- Ua = U5 A
  -- Ub = U5 C
  -- Uc = U5 B

  instance Semigroup M3 where
      -- A < B < C
      (<>) = max
  instance Monoid M3 where
      mempty = A

  instance Monad U5 where
      pure x = U5 mempty x x
      join (U5 a (U5 b x1 y1) (U5 _ _ y2)) =
          let z1 = case a of
              A -> x1
              B -> x1
              C -> y1
          in U5 (a <> b) z1 y2
  ```

* `Monad_6` case

  ```haskell
  data M4 = A | B | C
      deriving (Eq, Ord)
  data U6 a = U6 M4 a a

  -- Ua = U6 A
  -- Ub = U6 B
  -- Uc = U6 C

  instance Semigroup M4 where
      A <> y = y
      B <> _ = B
      C <> _ = C
  instance Monoid M4 where
      mempty = A

  instance Monad U6 where
      pure x = U6 mempty x x
      join (U6 a (U6 b x1 y1) (U6 _ _ y2)) =
          let z1 = case a of
                A -> x1
                B -> y1
                C -> y1
          in U6 (a <> b) z1 y2
  ```