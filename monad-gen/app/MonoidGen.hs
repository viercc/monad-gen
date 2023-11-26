{-# LANGUAGE KindSignatures #-}
module MonoidGen(
  -- * Generate Monoids
  MonoidOn(..), genMonoids,

  -- * Internals
  Env, makeEnv, fakeEnv, fromDef, genMonoidDefs
) where

import Data.Equivalence.Monad
import Data.Kind (Type)
import Data.List (sortOn, sort, maximumBy)
import Data.Maybe (mapMaybe)

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Lazy as Map

import Data.PTraversable
import Data.PTraversable.Extra

import qualified Data.Vector as V

import Data.Ord (comparing)
import Data.Foldable (Foldable(..), for_)

import Data.FunctorShape

-- Generate all possible monoids on @Shape f@, compatible with @Monad f@, up to iso

data MonoidOn f = MonoidOn
  { monoidUnit :: Shape f,
    monoidMult :: Shape f -> Shape f -> Shape f
  }

genMonoids :: (PTraversable f) => [MonoidOn f]
genMonoids = fromDef env <$> genMonoidDefs env
  where
    env = makeEnv

data Def (f :: Type -> Type) = Def !Int !(V.Vector Int)
  deriving (Show)

data Env f = Env {
    envKeys :: V.Vector (Shape f),
    envLengths :: V.Vector Int
    }

envSize :: Env f -> Int
envSize = length . envLengths

makeEnv :: (PTraversable f) => Env f
makeEnv = Env keys lengths
  where
    (keys, lengths) = V.unzip $ V.fromList $ sortOn snd [(Shape f1, length f1) | f1 <- shapes]

fakeEnv :: [Int] -> Env f
fakeEnv ns =
    let ns' = sort ns
        ls = V.fromList ns'
        keys = undefined <$> ls
    in Env keys ls

fromDef :: WeakOrd f => Env f -> Def f -> MonoidOn f
fromDef env (Def e mult) = MonoidOn (toKey e) op
  where
    n = envSize env
    revTable = Map.fromList [(f_, i) | (i, f_) <- V.toList (V.indexed (envKeys env))]
    toKey = (envKeys env V.!)
    fromKey = (revTable Map.!)
    op f1 f2 = toKey $ mult V.! (fromKey f1 * n + fromKey f2)

genMonoidDefs :: Env f -> [Def f]
genMonoidDefs env = do
  e <- unitCandidates
  let mults = mapMaybe (multMapToVec n) (gen n numZeroes e)
  mult <- upToIso env e mults
  pure (Def e mult)
  where
    n = envSize env
    lengths = V.toList $ envLengths env
    numZeroes = length $ takeWhile (== 0) lengths
    unitCandidates =
      [x | (x, lenX', lenX) <- zip3 [0 ..] (0 : lengths) lengths, lenX' < lenX]

multMapToVec :: Int -> MultTable -> Maybe (V.Vector Int)
multMapToVec n multMap = V.generateM (n * n) (\i -> Map.lookup (quotRem i n) multMap)

type MultTable = Map (Int, Int) Int

data KnownEq = KnownEq Int Int Int
    deriving (Show, Eq, Ord)
data AssocEq = AssocEq Int Int Int
    deriving (Show, Eq, Ord)

newtype Blocker = Blocker (Map (Int,Int) (Set AssocEq))
  deriving (Show, Eq)

instance Semigroup Blocker where
    Blocker m1 <> Blocker m2 = Blocker (Map.unionWith Set.union m1 m2)

instance Monoid Blocker where
    mempty = Blocker Map.empty

singleBlocker :: (Int,Int) -> AssocEq -> Blocker
singleBlocker xy eqn = Blocker $ Map.singleton xy (Set.singleton eqn)

checkEquation :: MultTable -> AssocEq -> Maybe ([KnownEq], Blocker)
checkEquation table eqn@(AssocEq x y z) =
    case (op x y, op y z) of
        (Right xy, Right yz) -> case (op xy z, op x yz) of
            (Right xyz1, Right xyz2)
              | xyz1 == xyz2 -> Just ([], mempty)
              | otherwise    -> Nothing
            (Left _, Right xyz) -> Just ([KnownEq xy z xyz], mempty)
            (Right xyz, Left _) -> Just ([KnownEq x yz xyz], mempty)
            (Left blockL, Left blockR)  -> Just ([], singleBlocker blockL eqn <> singleBlocker blockR eqn)
        (resL, resR) ->
            let blocksL = getLeft $ resL >>= \xy -> op xy z
                blocksR = getLeft $ resR >>= \yz -> op x yz
                blocks = foldMap (\b -> singleBlocker b eqn) (blocksL ++ blocksR)
            in Just ([], blocks)
    where
        op a b = case Map.lookup (a,b) table of
            Nothing -> Left (a,b)
            Just ab -> Right ab
        
        getLeft (Left a) = [a]
        getLeft (Right _) = []

checkEquations :: Foldable t => MultTable -> t AssocEq -> Maybe ([KnownEq], Blocker)
checkEquations table eqs = fold <$> traverse (checkEquation table) (toList eqs)

-- | Get the "most wanted" cell of the multiplication table
mostWanted :: Blocker -> Maybe (Int,Int)
mostWanted (Blocker m)
  | Map.null m = Nothing
  | otherwise = Just k
  where
    (k,_) = maximumBy (comparing (Set.size . snd)) $ Map.toList m

gen :: Int -> Int -> Int -> [MultTable]
gen n numZeroes e = go initialTable initialEqn initialBlocker
  where
    xs = [0 .. n - 1]
    zeroes = [0 .. numZeroes - 1]
    nonzeroes = filter (/= e) [numZeroes .. n - 1]
    initialTable =
      Map.fromList $
        [ ((z, y), z) | z <- zeroes, y <- xs]
          ++ [ ((e, x), x) | x <- xs]
          ++ [ ((x, e), x) | x <- nonzeroes]
    
    allAssocEq = [ AssocEq x y z | x <- nonzeroes, y <- nonzeroes, z <- xs, z /= e ]
    (initialEqn, initialBlocker) = case checkEquations initialTable allAssocEq of
        Nothing -> error "Bad initial table?"
        Just updates -> updates
    
    go table (KnownEq x y xy : eqs) blocker = case Map.lookup (x,y) table of
        Nothing -> do
            (table', newEqs, blocker') <- enter table (KnownEq x y xy) blocker
            go table' (newEqs ++ eqs) blocker'
        Just xy' | xy == xy' -> go table eqs blocker
                 | otherwise -> []
    go table [] blocker = case mostWanted blocker of
        Nothing -> [table]
        Just (x,y) ->
            do z <- guess x y
               (table', newEqs, blocker') <- enter table (KnownEq x y z) blocker
               go table' newEqs blocker'
    
    enter table (KnownEq x y z) (Blocker m) =
        case Map.lookup (x,y) m of
            Nothing -> [(table', [], Blocker m)]
            Just eqs -> case checkEquations table' eqs of
                Nothing -> []
                Just (newEqs, newBlockers) ->
                    [(table', newEqs, newBlockers <> Blocker (Map.delete (x,y) m))]
        where
            table' = Map.insert (x,y) z table

    guess _ y = if y < numZeroes then zeroes else xs


upToIso :: Env f -> Int -> [V.Vector Int] -> [V.Vector Int]
upToIso env e tabs = runEquivM id min $ do
  for_ tabs $ \mm -> do
    equate mm mm
  for_ (isoGenerators env e) $ \tr ->
    for_ tabs $ \mm -> equate mm (applyTranspose n tr mm)
  classes >>= traverse desc
  where
    n = envSize env

data Transposition = Transpose Int Int
  deriving (Show)

isoGenerators :: Env f -> Int -> [Transposition]
isoGenerators env e =
  [Transpose i j | ((i, n), (j, m)) <- zip lengths' (drop 1 lengths'), n == m]
  where
    lengths = V.toList $ V.indexed (envLengths env)
    lengths' = filter ((/= e) . fst) lengths

applyTranspose :: Int -> Transposition -> V.Vector Int -> V.Vector Int
applyTranspose n (Transpose a b) xs = V.generate (n * n) $ \i ->
  let (j, k) = quotRem i n
      i' = tr j * n + tr k
   in tr (xs V.! i')
  where
    tr i
      | i == a = b
      | i == b = a
      | otherwise = i
