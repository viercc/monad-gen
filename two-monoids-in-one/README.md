# two-monoids-in-one

`TwoMonoids` type class and its subclasses

- `TwoMonoids`: `Monoid` and another, independent set of monoid operations `zero, <+>`
  - `LZ`: + _left zero_ law `zero <> a === zero`
    - `NearSemiring`: + _left distribution_ law `(a <+> b) <> c === (a <> c) <+> (b <> c)`
    - `LZLC`: + _left catch_ law `mempty <+> a === mempty`
