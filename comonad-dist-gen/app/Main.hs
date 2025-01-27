{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Main(main) where

import Data.Coerce (coerce)
import Data.Foldable (for_)
import Control.Arrow ((&&&))
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import StoreDistributiveLaw
import Data.Finitary.Extra (prettyPrintFn2, prettyPrintFn)
import Data.Finitary (Finitary)

import Data.ZMod (Bit(..), ZMod)
import Data.Group
import Data.Finite (Finite)

newtype A = A Bit
  deriving newtype (Show, Read, Eq, Ord, Finitary)

newtype B = B Bit
  deriving newtype (Show, Read, Eq, Finitary)

main :: IO ()
main = printHandcraftedDistLens

generateAllDistLaws :: IO ()
generateAllDistLaws = mapM_ (print . encodeLens) $ filter checkAllLaws (generateCandidateLenses @A @B ())

{- Output (took about 18 min.):

makeLensEnc' [(0,39),(0,54),(4,54),(4,39),(3,39),(7,99),(3,99),(7,39)]
makeLensEnc' [(0,39),(1,57),(6,198),(4,39),(3,39),(5,147),(2,108),(7,39)]
makeLensEnc' [(1,45),(0,54),(4,54),(6,135),(2,45),(7,99),(3,99),(5,135)]
makeLensEnc' [(1,45),(1,57),(6,198),(6,135),(2,45),(5,147),(2,108),(5,135)]

-}

generatedData :: [ LensEnc (C A A B) (A,B) (C B B A) (B,A) ]
generatedData =
  [
    makeLensEnc' [(0,39),(0,54),(4,54),(4,39),(3,39),(7,99),(3,99),(7,39)]
  , makeLensEnc' [(0,39),(1,57),(6,198),(4,39),(3,39),(5,147),(2,108),(7,39)]
  , makeLensEnc' [(1,45),(0,54),(4,54),(6,135),(2,45),(7,99),(3,99),(5,135)]
  , makeLensEnc' [(1,45),(1,57),(6,198),(6,135),(2,45),(5,147),(2,108),(5,135)]
  ]

prettyPrintDistLenses :: IO ()
prettyPrintDistLenses = for_ (zip [0 :: Int ..] generatedData) $ \(i, encLens) -> do
  let lens = decodeLens encLens
  putStrLn $ "Dist #" ++ show i
  for_ (prettyPrintDistLens lens) $ \pprLine ->
    putStrLn $ "  " ++ pprLine

{- Output:

Dist #0
  let q (0,0,0) = (0,0,0)
      q (0,0,1) = (0,0,0)
      q (0,1,0) = (1,0,0)
      q (0,1,1) = (1,0,0)
      q (1,0,0) = (0,1,1)
      q (1,0,1) = (1,1,1)
      q (1,1,0) = (0,1,1)
      q (1,1,1) = (1,1,1)
      d0_5 (0,0) = 0
      d0_5 (0,1) = 1
      d0_5 (1,0) = 0
      d0_5 (1,1) = 1
      d0 (0,0,0) = d0_5
      d0 (0,0,1) = d0_5
      d0 (0,1,0) = d0_5
      d0 (0,1,1) = d0_5
      d0 (1,0,0) = d0_5
      d0 (1,0,1) = d0_5
      d0 (1,1,0) = d0_5
      d0 (1,1,1) = d0_5
      d1_3 (0,0) = 0
      d1_3 (0,1) = 0
      d1_3 (1,0) = 1
      d1_3 (1,1) = 1
      d1_6 (0,0) = 0
      d1_6 (0,1) = 1
      d1_6 (1,0) = 1
      d1_6 (1,1) = 0
      d1_9 (0,0) = 1
      d1_9 (0,1) = 0
      d1_9 (1,0) = 0
      d1_9 (1,1) = 1
      d1 (0,0,0) = d1_3
      d1 (0,0,1) = d1_6
      d1 (0,1,0) = d1_6
      d1 (0,1,1) = d1_3
      d1 (1,0,0) = d1_3
      d1 (1,0,1) = d1_9
      d1 (1,1,0) = d1_9
      d1 (1,1,1) = d1_3
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))
Dist #1
  let q (0,0,0) = (0,0,0)
      q (0,0,1) = (0,0,1)
      q (0,1,0) = (1,1,0)
      q (0,1,1) = (1,0,0)
      q (1,0,0) = (0,1,1)
      q (1,0,1) = (1,0,1)
      q (1,1,0) = (0,1,0)
      q (1,1,1) = (1,1,1)
      d0_5 (0,0) = 0
      d0_5 (0,1) = 1
      d0_5 (1,0) = 0
      d0_5 (1,1) = 1
      d0_6 (0,0) = 0
      d0_6 (0,1) = 1
      d0_6 (1,0) = 1
      d0_6 (1,1) = 0
      d0_9 (0,0) = 1
      d0_9 (0,1) = 0
      d0_9 (1,0) = 0
      d0_9 (1,1) = 1
      d0 (0,0,0) = d0_5
      d0 (0,0,1) = d0_6
      d0 (0,1,0) = d0_9
      d0 (0,1,1) = d0_5
      d0 (1,0,0) = d0_5
      d0 (1,0,1) = d0_9
      d0 (1,1,0) = d0_6
      d0 (1,1,1) = d0_5
      d1_3 (0,0) = 0
      d1_3 (0,1) = 0
      d1_3 (1,0) = 1
      d1_3 (1,1) = 1
      d1_5 (0,0) = 0
      d1_5 (0,1) = 1
      d1_5 (1,0) = 0
      d1_5 (1,1) = 1
      d1_10 (0,0) = 1
      d1_10 (0,1) = 0
      d1_10 (1,0) = 1
      d1_10 (1,1) = 0
      d1 (0,0,0) = d1_3
      d1 (0,0,1) = d1_5
      d1 (0,1,0) = d1_10
      d1 (0,1,1) = d1_3
      d1 (1,0,0) = d1_3
      d1 (1,0,1) = d1_5
      d1 (1,1,0) = d1_10
      d1 (1,1,1) = d1_3
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))
Dist #2
  let q (0,0,0) = (0,0,1)
      q (0,0,1) = (0,0,0)
      q (0,1,0) = (1,0,0)
      q (0,1,1) = (1,1,0)
      q (1,0,0) = (0,1,0)
      q (1,0,1) = (1,1,1)
      q (1,1,0) = (0,1,1)
      q (1,1,1) = (1,0,1)
      d0_5 (0,0) = 0
      d0_5 (0,1) = 1
      d0_5 (1,0) = 0
      d0_5 (1,1) = 1
      d0_6 (0,0) = 0
      d0_6 (0,1) = 1
      d0_6 (1,0) = 1
      d0_6 (1,1) = 0
      d0_9 (0,0) = 1
      d0_9 (0,1) = 0
      d0_9 (1,0) = 0
      d0_9 (1,1) = 1
      d0 (0,0,0) = d0_6
      d0 (0,0,1) = d0_5
      d0 (0,1,0) = d0_5
      d0 (0,1,1) = d0_9
      d0 (1,0,0) = d0_6
      d0 (1,0,1) = d0_5
      d0 (1,1,0) = d0_5
      d0 (1,1,1) = d0_9
      d1_3 (0,0) = 0
      d1_3 (0,1) = 0
      d1_3 (1,0) = 1
      d1_3 (1,1) = 1
      d1_6 (0,0) = 0
      d1_6 (0,1) = 1
      d1_6 (1,0) = 1
      d1_6 (1,1) = 0
      d1_9 (0,0) = 1
      d1_9 (0,1) = 0
      d1_9 (1,0) = 0
      d1_9 (1,1) = 1
      d1 (0,0,0) = d1_3
      d1 (0,0,1) = d1_6
      d1 (0,1,0) = d1_6
      d1 (0,1,1) = d1_3
      d1 (1,0,0) = d1_3
      d1 (1,0,1) = d1_9
      d1 (1,1,0) = d1_9
      d1 (1,1,1) = d1_3
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))
Dist #3
  let q (0,0,0) = (0,0,1)
      q (0,0,1) = (0,0,1)
      q (0,1,0) = (1,1,0)
      q (0,1,1) = (1,1,0)
      q (1,0,0) = (0,1,0)
      q (1,0,1) = (1,0,1)
      q (1,1,0) = (0,1,0)
      q (1,1,1) = (1,0,1)
      d0_6 (0,0) = 0
      d0_6 (0,1) = 1
      d0_6 (1,0) = 1
      d0_6 (1,1) = 0
      d0_9 (0,0) = 1
      d0_9 (0,1) = 0
      d0_9 (1,0) = 0
      d0_9 (1,1) = 1
      d0 (0,0,0) = d0_6
      d0 (0,0,1) = d0_6
      d0 (0,1,0) = d0_9
      d0 (0,1,1) = d0_9
      d0 (1,0,0) = d0_6
      d0 (1,0,1) = d0_9
      d0 (1,1,0) = d0_6
      d0 (1,1,1) = d0_9
      d1_3 (0,0) = 0
      d1_3 (0,1) = 0
      d1_3 (1,0) = 1
      d1_3 (1,1) = 1
      d1_5 (0,0) = 0
      d1_5 (0,1) = 1
      d1_5 (1,0) = 0
      d1_5 (1,1) = 1
      d1_10 (0,0) = 1
      d1_10 (0,1) = 0
      d1_10 (1,0) = 1
      d1_10 (1,1) = 0
      d1 (0,0,0) = d1_3
      d1 (0,0,1) = d1_5
      d1 (0,1,0) = d1_10
      d1 (0,1,1) = d1_3
      d1 (1,0,0) = d1_3
      d1 (1,0,1) = d1_5
      d1 (1,1,0) = d1_10
      d1 (1,1,1) = d1_3
  in  Lens $ \c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))

-}

printIsoTable :: IO ()
printIsoTable = mapM_ (putStrLn . List.intercalate "|" . map toSymb) isoTable
  where
    toSymb b = if b then "==" else "  "

{- Output:

==|  |  |  
  |==|  |  
  |  |==|  
  |  |  |==

Interpretation:
  The generated distributed laws are not "isomorphic" each other

-}

printHandcraftedDistLens :: IO ()
printHandcraftedDistLens = do
  putStrLn "### Dist0"
  putStrLn $ "Code:     " ++ show (encodeLens distLens0)
  putStrLn $ "Validity: " ++ show (checkAllLaws distLens0)
  putStrLn $ "Is dist0 correct? " ++ show (distToLens dist0 == distLens0)
  putStrLn $ "Is distByGroup correct? " ++ show (distToLens distByGroup == distLens0)

  putStrLn "### distByGroup"
  let distByGroup_2_3 = distToLens (distByGroup @(Finite 2) @(ZMod 3))
  putStrLn $ "dist := distByGroup @(Finite 2) @(ZMod 3)"
  putStrLn $ "Code: " ++ show (encodeLens distByGroup_2_3)
  putStrLn $ "Validity: " ++ show (checkAllLaws distByGroup_2_3)

  putStrLn "### Dist1"
  putStrLn $ "Code:     " ++ show (encodeLens distLens1)
  putStrLn $ "Validity: " ++ show (checkAllLaws distLens1)
  -- putStrLn $ "Is dist1 correct? " ++ show (distToLens dist1 == distLens1)
{-

### Dist0
Code:     makeLensEnc' [(0,39),(0,54),(4,54),(4,39),(3,39),(7,99),(3,99),(7,39)]
Validity: True
Is dist0 correct? True
### Dist1
Code:     makeLensEnc' [(0,39),(1,57),(6,198),(4,39),(3,39),(5,147),(2,108),(7,39)]
Validity: True

-}

prettyPrintDistLens :: DistLens A B -> [String]
prettyPrintDistLens l =
  pprLetIn (prettyPrintFn "q" q ++ prettyPrintFn2 "d0" d0 ++ prettyPrintFn2 "d1" d1) [ "Lens $ \\c -> ((review . q . view) c, d0 (view c) &&& d1 (view c))" ]
  where
    q :: (A,B,B) -> (B,A,A)
    q = view . coerce . fst . unLens l . coerce . review 
    
    d0 :: (A,B,B) -> (B,A) -> A
    d0 = fmap fst . snd . unLens l . coerce . review

    d1 :: (A,B,B) -> (B,A) -> B
    d1 = fmap snd . snd . unLens l . coerce . review

    indent = ("    " ++)
    pprLetIn _ [] = error "empty let-body?"
    pprLetIn [] _ = error "empty let-defs?"
    pprLetIn (firstDefLine : letLines) (firstBodyLine : inLines) =
      ["let " ++ firstDefLine]
       ++ map indent letLines
       ++ [ "in  " ++ firstBodyLine ]
       ++ map indent inLines
    
    view :: C a Bit b -> (a,b,b)
    view (C a f) = (a, f 0, f 1)

    review :: (a,b,b) -> C a Bit b
    review (a, b0, b1) = C a $ \bit -> if bit == 0 then b0 else b1

-- | Comonad automorphism
--
-- Every comonad automorphism of a store comonad @C S S@
-- come from an automorphism @(σ :: S -> S)@, as
-- @mapPos σ . mapPort σ⁻¹@
--
-- There's only one automorphism @Bool -> Bool@ that isn't @id@: @notBit@.
comonadAuto :: forall x. C Bit Bit x -> C Bit Bit x
comonadAuto = mapPos (1+) . mapPort (1+)

translate :: DistLens A B -> [DistLens A B]
translate l =
    [ distToLens (actB gB . fmap (actA gA) . dist . fmap (actB (inv gB)) . actA (inv gA))
      | (gA, gB) <- actions ]
  where
    dist :: Dist A B
    dist = distFromLens l

    actions = [ (gA, gB) | gA <- [False, True], gB <- [False, True], gA || gB ]
    inv = id

    actA :: forall x. Bool -> C A A x -> C A A x
    actA b = if b then coerce (comonadAuto @x) else id

    actB :: forall x. Bool -> C B B x -> C B B x
    actB = coerce (actA @x)

isoTable :: [[Bool]]
isoTable = [[ isIso i j | j <- [0..n-1]] | i <- [0 .. n-1]]
  where
    n = length generatedData
    revMap = Map.fromList (zip generatedData [0..])
    isoList = do
      (encLens, i) <- Map.toList revMap
      let lens = decodeLens encLens
      otherLens <- translate lens
      let encOtherLens = encodeLens otherLens
      case Map.lookup encOtherLens revMap of
        Nothing -> error "what!?"
        Just j -> pure (i,j)
    isoRelation = Set.fromList isoList
    isIso i j = i == j || (i,j) `Set.member` isoRelation

-- Simplify and Dist #0 as A = B = Bool
distLens0 :: DistLens Bit Bit
distLens0 = Lens $ \c -> (q c, d0 c &&& d1 c)
  where
    q (C a f) = C (f a) (const a)
    d0 _ (_,a) = a
    d1 (C a0 f) (b,a) = b - f a0 + f a

-- dist0 = distFromLens distLens0
dist0 :: Dist Bit Bit
dist0 (C a0 k) = C (f a0) $ \b -> C a0 $ \a -> h a (b - f a0 + f a)
  where
    f = pos . k
    h a b = peek (k a) b

distLens1 :: DistLens Bit Bit
distLens1 = Lens $ \c -> (q c, d0 (view c) &&& d1 (view c))
  where
    view (C a0 f) = (a0, f 0, f 1)

    q (C 0 f) = C (f 0) $ \b -> if f b >  f (1 + b) then 1 else 0
    q (C _ f) = C (f 1) $ \b -> if f b >= f (1 + b) then 1 else 0

    d0_5 (_,a) = a
    d0_6 (b,a) = b + a
    d0_9 (b,a) = 1 + b + a

    d0 (0,0,0) = d0_5
    d0 (0,0,1) = d0_6
    d0 (0,1,0) = d0_9
    d0 (0,1,1) = d0_5
    d0 (1,0,0) = d0_5
    d0 (1,0,1) = d0_9
    d0 (1,1,0) = d0_6
    d0 (1,1,1) = d0_5
    d0 _ = undefined
    
    d1_3 (b,_) = b
    d1_5 (_,a) = a
    d1_10 (_,a) = 1 + a
    
    d1 (0,0,0) = d1_3
    d1 (0,0,1) = d1_5
    d1 (0,1,0) = d1_10
    d1 (0,1,1) = d1_3
    d1 (1,0,0) = d1_3
    d1 (1,0,1) = d1_5
    d1 (1,1,0) = d1_10
    d1 (1,1,1) = d1_3
    d1 _ = undefined

-- | Distributive law by group
distByGroup :: forall a g. Group g => Dist a g
distByGroup (C a0 k) = C (f a0) $ \g -> C a0 $ \a -> h a (g <> invert (f a0) <> f a)
  where
    f = pos . k
    h a b = peek (k a) b