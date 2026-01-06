{-# LANGUAGE DeriveTraversable #-}
module Main where

import qualified Data.Set as Set

data T a = Pure a | T01 a a a | T10 a a a | T00 a a a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Location = Bot | A | B
  deriving (Show, Eq)

run :: T a -> Location -> (Location, a)
run (Pure x) loc = (loc, x)
run (T01 x0 xa xb) loc = case loc of
  Bot -> (Bot, x0)
  A   -> (Bot, xa)
  B   -> (B,   xb)
run (T10 x0 xa xb) loc = case loc of
  Bot -> (Bot, x0)
  A   -> (A,   xa)
  B   -> (Bot, xb)
run (T00 x0 xa xb) loc = case loc of
  Bot -> (Bot, x0)
  A   -> (Bot, xa)
  B   -> (Bot, xb)

fromState :: (Location -> (Location, a)) -> T a
fromState f = case move0 `seq` (moveA, moveB) of
  (False, False) -> Pure x0
  (False, True)  -> T10 x0 xa xb
  (True, False)  -> T01 x0 xa xb
  (True, True)   -> T00 x0 xa xb
  where
    (l0, x0) = f Bot
    (la, xa) = f A
    (lb, xb) = f B
    move0 = if l0 == Bot then () else error $ "invalid move " ++ show (Bot, l0)
    moveA = case la of
      Bot -> True
      A   -> False
      B   -> error "invalid move (A, B)"
    moveB = case lb of
      Bot -> True
      A   -> error "invalid move (B, A)"
      B   -> False

pure_ :: a -> T a
pure_ = Pure

join_ :: T (T a) -> T a
join_ ttx = fromState joinState
  where
    joinState loc =
      let (loc', tx) = run ttx loc
      in run tx loc'

binaryJoin :: T Bool -> T a -> T a -> T a
binaryJoin x y y' = join_ (fmap (\b -> if b then y' else y) x)

binaryJoinResults :: [T Int]
binaryJoinResults = binaryJoin <$> xs <*> ys <*> ys'
  where
    bs = [ False, True ]
    constructors = [T01 False, T10 False, T00 False]
    xs = [ Pure False ] ++ (constructors <*> bs <*> bs)
    -- Because @binaryJoin (not <$> x)@ is determined by @binaryJoin x@, 
    -- let (b0 = False) w.l.o.g.
    
    ys = fmap (\b -> if b then 1 else 0) <$> xs
    ys' = fmap (fmap (+ 2)) ys

main :: IO ()
main = mapM_ print $ Set.fromList $ binaryJoinResults