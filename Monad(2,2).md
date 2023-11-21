How many instances of `Monad T` are there, up to natural isomorphisms on `T`?

```haskell
data T x = T Bool x x
pure :: x -> T x
join :: T (T x) -> T x
```

Answer: 3. Any lawful `Monad T` is isomorphic to one of them:

1. The one isomorphic to `Product (Writer Xor) Identity`

   ```haskell
   pure x = T False x x
   join ttx = case ttx of
       T b (T b' x0 _) (T _ _ x3) -> T (b `xor` b'') x0 x3
   ```

2. The one isomorphic to `Product (Writer Any) Identity`

   ```haskell
   pure x = T False x x
   join ttx = case ttx of
       T b (T b' x0 _) (T _ _ x3) -> T (b || b'') x0 x3
   ```

3. The one you can't decompose to `Product` of two monads.

   ```haskell
   pure x = T False x x
   join ttx = case ttx of
       T False (T b' x0 _) (T _ _ x3) -> T b' x0 x3
       T True  (T _  _ x1) (T _ _ x3) -> T True x1 x3
   ```

   This is a sub-monad of `State Bool` by the following inclusion:

   ```haskell
   newtype State s x = State { runState :: s -> (s, x) }

   incl :: T x -> State Bool x
   incl (T False x0 x1) = State $ \s -> (s, bool x0 x1 s)
   incl (T True  x0 x1) = State $ \s -> (True, bool x0 x1 s)

   bool :: a -> a -> Bool -> a
   bool x0 x1 s = case s of
       False -> x0
       True  -> x1
   ```
