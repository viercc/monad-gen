
```haskell
{
    data T a = T Bool x x
    pure x = T False x x
    join ttx = case ttx of
        T b (T b' x0 _) (T _ _ x3) -> T (b `xor` b'') x0 x3
}
```

```haskell
{
    data T a = T Bool x x
    pure x = T False x x
    join ttx = case ttx of
        T b (T b' x0 _) (T _ _ x3) -> T (b || b'') x0 x3
}
```

```haskell
{
    data T a = T Bool x x
    pure x = T False x x
    join ttx = case ttx of
        T False (T b' x0 _) (T _ _ x3) -> T b' x0 x3
        T True  (T _  _ x1) (T _ _ x3) -> T True x1 x3
}
```