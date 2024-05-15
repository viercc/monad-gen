次の`F`の形をした`Monad`について考える。

```
M :: Type
E :: Type

newtype F a = F (M, E -> a)

instance Monad F
```

`F`が`Monad`であったならば、`M`はモノイド構造を持っている。

```
π1 :: F a -> M
π1 (F (m,_)) = m

π2 :: F a -> (E -> a)
π2 (F (_,f)) = f

instance Monoid M where
  -- pure = return
  mempty = π1 (pure ())
  -- (<*>) = ap 
  m1 <> m2 = π1 $ F (m1, const ()) <*> F (m2, const ())
```

`pure`の実装は一つに定まる。

```
-- mempty と書くのが煩わし過ぎるので、以降 1 と書く。
-- 正しいHaskellではないが、まあわかってほしい。
pure :: a -> F a
pure a = F (1, const a)
```

また、`join`の実装は、次のように与えられた関数`α`と`δ`によって定まることを確認する。

```
con :: (M, E -> M, (E, E) -> a) -> F (F a)
con (m0, m1, g) = F (m0, \i -> F (m1 i, \j -> g (i, j)))

decon :: F (F a) -> (M, E -> M, (E, E) -> a)
decon (F (m0, f)) = (m0, π1 . f, π2 . f)

join :: F (F a) -> F a
join ffa =
  let (m0, m1, g) = decon ffa
  in F (α m0 m1, g . δ m0 m1)

α :: M -> (E -> M) -> M
α m0 m1 = π1 . join $ con (m0, m1, id)

δ :: M -> (E -> M) -> E -> (E, E)
δ m0 m1 = π2 . join $ con (m0, m1, id)
```

`Monad`則を`α`と`δ`を使って書き直すことができる。

```
-- [Left Unit]
-- join . pure = id
join $ pure (F (m, f))
 = join $ F (1, const (F (m, f)))
 = F (α 1 (const m), (\(i,j) -> f j) . δ 1 (const m))
 = F (m, f)

α 1 (const m) = m          -- (A1)
snd . δ 1 (const m) = id   -- (D1)
δ 1 (const m) i = (dr m i, i)


-- [Right Unit]
-- join . fmap pure = id
join $ fmap pure (F (m, f))
 = join $ F (m, \i -> F (1, const (f i)))
 = F (α m (const 1), (\(i, j) -> f i) . δ m (const 1))
 = F (m, f)

α m (const 1) = m          -- (A2)
fst . δ m (const 1) = id   -- (D2)
δ m (const 1) i = (i, dl m i)

-- From (D1), (D2):
δ 1 (const 1) = \i -> (i,i)

-- [Assoc]
-- join . join = join . fmap join

-- 詳細は省略するが、次の同型
--   decon' :: F (F (F a)) -> (M, E -> M, (E, E) -> M, ((E, E), E) -> a)
--   con'   :: F (F (F a)) <- (M, E -> M, (E, E) -> M, ((E, E), E) -> a)
-- を使って記述する。

join . join $ con' (m0, m1, m2, f)
 = join $ F (α m0 m1, (\(i,j) -> F (m2 i j, f . ((i,j),))) . δ m0 m1)
 = let d = δ m0 m1
   in  F (α (α m0 m1) (m2 . d),
          f . first d . δ (α m0 m1) (m2 . d))

join . fmap join $ con' (m0, m1, m2, f)
 = join $ F (m0, \i ->
     F (α (m1 i) (m2 . (i,)),
        (\(j,k) -> f ((i,j),k)) . δ (m1 i) (m2 . (i,)))
 = let m1' i = α (m1 i) (m2 . (i,))
   in  F (α m0 m1',
          f . assoc . extend (\i -> δ (m1 i) (m2 . (i,))) . δ m0 m1')

assoc :: (a, (b,c)) -> ((a,b), c)
extend :: (a -> b -> c) -> (a,b) -> (a,c)
extend f (a,b) = (a, f a b)

d = δ m0 m1
m1' i = α (m1 i, m2 . (i,))

α (α m0 m1) (m2 . d) = α m0 m1'                              -- (A3)
first d . δ (α m0 m1) (m2 . d)
= assoc . extend (\i -> δ (m1 i) (m2 . (i,))) . δ m0 m1'     -- (D3)
```

これは*複雑すぎる*ので、Applicativeな形から検討する。

```
-- parameters
x, y, z :: M
f :: E -> a
g :: E -> b
h :: E -> c

--
t :: F a
t = F (x, f)
u :: F b
u = F (y, g)
v :: F c
v = F (z, h)

x <> y = α x (const y)
d x y = δ x (const y)

prod = liftA2 (,)
prod (F (x, f)) (F (y, g))
 = join $ F (x, \i -> F (y, \j -> (f i, g j)))
 = F (α x (const y),
      (f *** g) . d x y)
 = F (x <> y, f *** g . d x y)

-- 左単位
prod (F (x,f)) (pure b) = (,b) <$> F (x, f)
prod (F (x,f)) (pure b)
 = F (x <> 1, (f *** const b) . d x 1)
 = (,b) . F (x,f)

x <> 1 = x
fst . d x 1 = id
d x 1 = id &&& dl x

-- 同様に右単位から
1 <> x = x
snd . d 1 x = id
d 1 x = dr x &&& id 

-- Applicativeの結合法則

-- 結合法則:
(t `prod` u) `prod` v
 = assoc $ t `prod` (u `prod` v)

(LHS)
  = F (x <> y, f *** g . δ x (const y)) `prod` v
  = F ((x <> y) <> z, (f *** g . δ x (const y)) *** h . δ (x <> y) (const z))
  = F ((x <> y) <> z,
       first (f *** g) . second h . first (δ x (const y)) . δ (x <> y) const z)
  = F ((x <> y) <> z,
       (f *** g) *** h . first (δ x (const y)) . δ (x <> y) const z)
(RHS)
  = ...(omit)...
  = F (x <> (y <> z),
       assoc . f *** (g *** h) . second (δ y (const z)) . δ x (const (y <> z)))

```

図に表すならば：

```
--|       |
  | d x y |---|              |
--|       |   |              |
              | d (x <> y) z |--
              |              |
--------------|              |

===================================

--------------|              |
              |              |
              | d x (y <> z) |--
--|       |   |              |
  | d y z |---|              |
--|       |

```

特に、`y=1`のときを考えると

```
first (d x 1) . d x z = assoc . second (d 1 z) . d x z
(id &&& dl x) *** id . d x z = assoc . id *** (dr z &&& id) . d x z

dl x . fst . d x z = dr z . snd . d x z
```

このようなApplicativeの具体例をいくつか構成する。
もっとも単純には、`F ~ Compose (M,) (E ->)`とすることができる。これは、

```
d _ _ = \i -> (i,i)
```

とした場合に外ならない。また、`M = Endo E ~ E -> E` であるとき、
自然同型 `F x  ~  (E -> E, E -> x)  ~  E -> (E, x)  ~  State E x`
が得られるが、`State E`は`Monad`であり、もちろん`Applicative`でもあるので、
`F x`が`Applicative`として得られたことになる。このとき、`d`は
```
d m _ = \i -> (i, appEndo m i)
```
である。

`State E`と同型になるケースとの中間例として、
`M`が`E`上にモノイド作用を持つ場合というものを考えることができる。
モノイド`M`の`E`上への(右)モノイド作用`(<|) :: E -> M -> E`は
```
x <| mempty = x
(x <| m1) <| m2 = x <| (m1 <> m2)
```
を満たす関数である。モノイド作用`<|`を用いて、

```
d m _ = \i -> (i, i <| m)
```

と書ける場合、これは`Applicative`則を満たす。特に結合則だけ書き下すなら、

```
first (d x y) . d (x <> y) z
     = \i -> ((i, i <| x), i <| (x <> y))
 = assoc . second (d y z) . d x (y <> z)
     = \i -> ((i, i <| x), i <| x <| y)
```

となり、`<|`がモノイド作用であることからこれらは等しくなる。

今考えたものは*右*モノイド作用であるが、*左*モノイド作用を考えることもできて、
左モノイド作用 `(|>) :: M -> E -> E` は次式を満たす。

```
mempty |> x = x
m1 |> (m2 |> x) = (m1 <> m2) |> x
```

これを用いて、

```
d _ m = \i -> (m |> i, i)
```

と書ける場合も`Applicative`則を満たす。結合法則は

```
first (d x y) . d (x <> y) z
     = \i -> ((y |> z |> i, z |> i), i)
 = assoc . second (d y z) . d x (y <> z)
     = \i -> (((y <> z) |> i, z |> i), i)
```

であり、左モノイド作用であることからこの等式が成り立つ。

さて、右モノイド作用と左モノイド作用の両方が定義されているとき、

```
d m1 m2 = \i -> (m2 |> i, i <| m1)
```

は結合法則を満たすだろうか？

```
first (d x y) . d (x <> y) z
     = \i -> (d x y $ z |> i, i <| (x <> y))
     = \i -> ((y |> z |> i, (z |> i) <| x), i <| (x <> y))
 = assoc . second (d y z) . d x (y <> z)
     = \i -> assoc ((y <> z) |> i, d y z $ i <| x)
     = \i -> ((y <> z) |> i, z |> (i <| x), i <| x <| y)
```
やや複雑だが、第1成分と第3成分はモノイド作用の結合則から等しい。しかし、第2成分
```
(z |> i) <| x = z |> (i <| x)
```
が等しいことは保証されていない！これは、右モノイド作用と左モノイド作用が可換である
必要があることを示している。

具体例を出してみよう。`M = E = Int`とし、`M`のモノイドは`Int`の加法とする。
```
x |> y = x <| y = x + y
```
とすれば、これは左右のモノイド作用を定めており、さらに互いに可換である。

```
d x y = \i -> (i + y, i + x)
```

であるから、Applicativeの定義式まで展開してみると、

```
newtype F x = F (Int, Int -> x)

instance Applicative F where
  pure x = F (0, const x)
  F (x, f) <*> F (y, g) = F (x + y, \i -> f (i + y) (g (i + x)))
```

である。こんなApplicativeは見たことさえないが、何かの役に立つだろうか？

```
tell :: M -> a -> F a
tell m a = F (m, const a)

ask :: (E -> a) -> F a
ask f = F (1, f)

pure = tell 1
join $ tell m1 (tell m2 a) = tell (m1 <> m2) a

join $ tell m (ask f)
 = join $ F (m, const $ F (1, f))
 = F (α m (const 1), f . snd . δ m (const 1))
 = F (m, f . dl m)

join $ ask (\i -> tell m (f i))
 = join $ F (1, \i -> F (m, const (f i)))
 = F (α 1 (const m), f . fst . δ 1 (const m))
 = F (m, f . dr m)

join $ ask (\i -> ask (\j -> f i j))
 = join $ F (1, \i -> F (1, f i))
 = F (α 1 (const 1), uncurry f . δ 1 (const 1))
 = F (1, \i -> f i i)
 = ask (\i -> f i i)
```

```
forall n1 :: E -> M
-- (A3), (D3)において、
m1 = const 1
m2 = n1 . fst
-- である場合を考えると、

d = δ m0 (const 1)
m1' i = α (const 1 i) (n1 . fst . (i,))
      = α 1 (const (n1 i))
      = n1 i
m1' = n1

m2 . d
 = n1 . fst . d
 = n1 . fst . δ m0 (const 1)
 = n1

α (α m0 m1) (m2 . d) = α m0 n1

first d . δ (α m0 m1) (m2 . d)
 = first (δ m0 (const 1)) . δ m0 n1

assoc . extend (\i -> δ (m1 i) (m2 . (i,))) . δ m0 m1'
 = assoc . extend (\i -> δ 1 (const (n1 i))) . δ m0 n1

δ m0 n1 i = (j, k)
first d (j, k) = ((j, dl m0 j), k)
extend (\i -> δ 1 (const (n1 i))) (j,k) = (j, (dr (n1 j) k, k))

dl m0 j = dr (n1 j) k -- (D4)
```

```
-- (A3), (D3)において、
m0 = 1
m1 = const 1
-- である場合を考えると、

d = δ m0 m1 = δ 1 (const 1) = \i -> (i,i)
m1' i = α (m1 i) (m2 . (i,)) = α 1 (m2 . (i,))

α (α m0 m1) (m2 . d)
 = α (α 1 (const 1)) (m2 . d)
 = α 1 (m2 . d)
α m0 m1'
 = α 1 (\i -> α 1 (m2 . (i,)))

α 1 (\i -> α 1 (h i)) = α 1 (\i -> h i i) -- (Au)

first d . δ (α m0 m1) (m2 . d)
 = first (\i -> (i,i)) . δ 1 (m2 . d)

extend (\i -> δ (m1 i) (m2 . (i,))) . δ m0 m1'
 = extend (\i -> δ 1 (m2 . (i,))) . δ 1 m1'

δ 1 (m2 . d) i = (j,k)

first (\i -> (i,i)) $ δ 1 (m2 . d) i
  = ((j, j), k)

extend (\i -> δ 1 (m2 . (i,))) $ δ 1 m1' i
  = (j', (k', l'))

* Case: m2 (_,j) = n1 j
  * δ 1 (m2 . d) i = δ 1 n1 i = (j, k)
  * m1' = const (α 1 n1)
  * δ 1 m1' i = (dr (α 1 n1) i, i)
  * δ 1 (m2 . (dr (α 1 n1) i,)) i = δ 1 n1 i = (j, k)
  * (j, j, k) = (dr (α 1 n1) i, j, k)
  * j = dr (α 1 n1) i

```


```
-- (A3), (D3)において、
m2 = const 1
-- である場合を考えると、

m = α m0 m1
d = δ m0 m1
m1' i = α (m1 i) (const 1 . (i,))
      = m1 i
m1' = m1

first d . δ (α m0 m1) (m2 . d)
 = first d . δ m (const 1 . d)
 = first d . (\i -> (i, dl m i))

assoc . extend (\i -> δ (m1 i) (m2 . (i,))) . δ m0 m1'
 = assoc . extend (\i -> δ (m1 i) (const 1)) . δ m0 m1
 = assoc . extend (\i j -> (j, dl (m1 i) j)) . d

d i = (j, k)
first d . (\i -> (i, dl m i)) $ i
 = (d i, dl m i) = ((j,k), dl m i)

extend (\i j -> (j, dl (m1 i) j)) $ d i
 = (j, (k, dl (m1 j) k))

dl m i = dl (m1 j) k
```

