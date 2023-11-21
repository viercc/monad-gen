```haskell
data T x = T Bool x x
```

```haskell
{
    pure 0 = Ta 0 0
    join $ Ta (Ta 0 1) (Ta 2 3) = Ta 0 3
    join $ Ta (Ta 0 1) (Tb 2 3) = Ta 0 3
    join $ Ta (Tb 0 1) (Ta 2 3) = Tb 0 3
    join $ Ta (Tb 0 1) (Tb 2 3) = Tb 0 3

    join $ Tb (Ta 0 1) (Ta 2 3) = Tb 0 3
    join $ Tb (Ta 0 1) (Tb 2 3) = Tb 0 3
    join $ Tb (Tb 0 1) (Ta 2 3) = Ta 0 3
    join $ Tb (Tb 0 1) (Tb 2 3) = Ta 0 3
}

{
    data T a = T Bool x x
    pure x = T False x x
    join ttx = case ttx of
        T b (T b' x0 _) (T _ _ x3) -> T (b `xor` b'') x0 x3
}
```

```haskell
{
    pure 0 = Ta 0 0
    join $ Ta (Ta 0 1) (Ta 2 3) = Ta 0 3
    join $ Ta (Ta 0 1) (Tb 2 3) = Ta 0 3
    join $ Ta (Tb 0 1) (Ta 2 3) = Tb 0 3
    join $ Ta (Tb 0 1) (Tb 2 3) = Tb 0 3
    join $ Tb (Ta 0 1) (Ta 2 3) = Tb 0 3
    join $ Tb (Ta 0 1) (Tb 2 3) = Tb 0 3
    join $ Tb (Tb 0 1) (Ta 2 3) = Tb 0 3
    join $ Tb (Tb 0 1) (Tb 2 3) = Tb 0 3
}

{
    data T a = T Bool x x
    pure x = T False x x
    join ttx = case ttx of
        T b (T b' x0 _) (T _ _ x3) -> T (b || b'') x0 x3
}
```

```haskell
{
    pure 0 = Ta 0 0
    join $ Ta (Ta 0 1) (Ta 2 3) = Ta 0 3
    join $ Ta (Ta 0 1) (Tb 2 3) = Ta 0 3
    join $ Ta (Tb 0 1) (Ta 2 3) = Tb 0 3
    join $ Ta (Tb 0 1) (Tb 2 3) = Tb 0 3
    join $ Tb (Ta 0 1) (Ta 2 3) = Tb 1 3
    join $ Tb (Ta 0 1) (Tb 2 3) = Tb 1 3
    join $ Tb (Tb 0 1) (Ta 2 3) = Tb 1 3
    join $ Tb (Tb 0 1) (Tb 2 3) = Tb 1 3
}

{
    data T a = T Bool x x
    pure x = T False x x
    join ttx = case ttx of
        T False (T b' x0 _) (T _ _ x3) -> T b' x0 x3
        T True  (T _  _ x1) (T _ _ x3) -> T True x1 x3
}
```