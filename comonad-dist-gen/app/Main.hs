module Main where

import StoreDistributiveLaw

main :: IO ()
main = mapM_ print $ lawfulDistLenses (candidateLenses ())

{-

Fn \case {
  C A₀ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₀ (const A₀),Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₁);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₀)});
  C A₀ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ (const A₀),Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₁ (const A₀),Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₁);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₀)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ (const A₀),Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ (const A₁),Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₁ (const A₁),Fn \case {(B₀,A₀) -> (A₀,B₁);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₀);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₀ (const A₁),Fn \case {(B₀,A₀) -> (A₀,B₁);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₀);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ (const A₁),Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)})
}
Fn \case {
  C A₀ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₀;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₀ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₀ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₁);(B₁,A₀) -> (A₁,B₀);(B₁,A₁) -> (A₀,B₁)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₁ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₁,B₁);(B₀,A₁) -> (A₀,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₀)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₀;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₁;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₁,B₀);(B₀,A₁) -> (A₀,B₁);(B₁,A₀) -> (A₀,B₀);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₁);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₁,B₁);(B₁,A₁) -> (A₀,B₀)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₁;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)})
}
Fn \case {
  C A₀ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₁,B₁);(B₁,A₁) -> (A₀,B₁)});
  C A₀ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₀ \case {B₀ -> A₀;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₁);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₀)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₁ \case {B₀ -> A₀;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₁);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₀)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₁,B₀);(B₀,A₁) -> (A₀,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₁,B₁);(B₁,A₁) -> (A₀,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₁;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₁);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₀);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₁;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₁);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₀,B₀);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₁,B₀);(B₀,A₁) -> (A₀,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)})
}
Fn \case {
  C A₀ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₁,B₁);(B₁,A₁) -> (A₀,B₁)});
  C A₀ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₀ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₁);(B₁,A₀) -> (A₁,B₀);(B₁,A₁) -> (A₀,B₁)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₁ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₁,B₁);(B₀,A₁) -> (A₀,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₀)});
  C A₀ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₁,B₀);(B₀,A₁) -> (A₀,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₀);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₁,B₁);(B₁,A₁) -> (A₀,B₁)});
  C A₁ \case {A₀ -> B₀;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₁,B₀);(B₀,A₁) -> (A₀,B₁);(B₁,A₀) -> (A₀,B₀);(B₁,A₁) -> (A₁,B₁)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₀} -> (C B₀ \case {B₀ -> A₁;B₁ -> A₀},Fn \case {(B₀,A₀) -> (A₀,B₁);(B₀,A₁) -> (A₁,B₀);(B₁,A₀) -> (A₁,B₁);(B₁,A₁) -> (A₀,B₀)});
  C A₁ \case {A₀ -> B₁;A₁ -> B₁} -> (C B₁ \case {B₀ -> A₀;B₁ -> A₁},Fn \case {(B₀,A₀) -> (A₁,B₀);(B₀,A₁) -> (A₀,B₀);(B₁,A₀) -> (A₀,B₁);(B₁,A₁) -> (A₁,B₁)})
}

-}