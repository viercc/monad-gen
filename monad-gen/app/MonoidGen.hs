{-# LANGUAGE KindSignatures #-}
module MonoidGen(
  -- * Generate Monoids
  MonoidDict(..),
  makeMonoidDict,
  
  MonoidData(..),
  genMonoids,
  genMonoidsWithSig,
  genMonoidsForApplicative,
  genMonoidsForMonad,
  prettyMonoidData,

  -- * Raw monoids
  RawMonoidData(..),
  prettyRawMonoidData,

  -- * Raw monoid generation
  Signature,
  genRawMonoids,
  genRawMonoidsForApplicative,
  genRawMonoidsForMonad,
  
  -- * Internals
  makeEnv, fakeEnv,
) where

import Data.Equivalence.Monad
import Data.List (sortOn, sort, maximumBy)
import Data.Maybe (mapMaybe)
import Data.Foldable (Foldable(..), for_)
import Data.Traversable.WithIndex (TraversableWithIndex(..))

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Lazy as Map

import Data.PTraversable

import qualified Data.Vector as V
import Data.Array ((!), Ix(..), Array)
import qualified Data.Array as Array

import Data.Ord (comparing)

import Data.FunctorShape
import Data.Transparent

-- * MonoidDict

data MonoidDict a = MonoidDict
  { monoidUnit :: a,
    monoidMult :: a -> a -> a
  }

makeMonoidDict :: Ord a => MonoidData a -> MonoidDict a
makeMonoidDict
  MonoidData{
    _elemTable = env,
    _rawMonoidData = RawMonoidData {
      _unitElem = e,
      _multTable = mult
    }
  } = MonoidDict (env V.! e) op
  where
    revTable = Map.fromList [(f_, i) | (i, f_) <- V.toList (V.indexed env)]
    fromKey = (revTable Map.!)
    op f1 f2 = env V.! (mult ! (fromKey f1, fromKey f2))


-- * MonoidData

data MonoidData a = MonoidData
  {
    _elemTable :: V.Vector a,
    _rawMonoidData :: RawMonoidData
  }

genMonoids :: (Transparent a) => [MonoidData a]
genMonoids = genMonoidsWithSig (const 1)

genMonoidsWithSig :: (Transparent a) => (a -> Int) -> [MonoidData a]
genMonoidsWithSig f = MonoidData env <$> genRawMonoids sig
  where
    (env, sig) = makeEnv f

genMonoidsForApplicative :: (PTraversable f) => [MonoidData (Shape f)]
genMonoidsForApplicative = MonoidData env <$> genRawMonoidsForApplicative sig
  where
    (env, sig) = makeEnv (\(Shape f1) -> length f1)

genMonoidsForMonad :: (PTraversable f) => [MonoidData (Shape f)]
genMonoidsForMonad = MonoidData env <$> genRawMonoidsForMonad sig
  where
    (env, sig) = makeEnv (\(Shape f1) -> length f1)

prettyMonoidData :: (Show a) => String -> MonoidData a -> [String]
prettyMonoidData monName monoidData =
  [monName ++ " = Monoid{"] ++
  map ("  " ++) (
    [ "Elements:" ] ++
    map indent (prettyElems env) ++
    [ "Unit element: " ++ show e ] ++
    [ "Multiplication table: " ] ++
    map indent (prettyArray (_multTable (_rawMonoidData monoidData)))
  ) ++
  ["}"]
  where
    env = _elemTable monoidData
    e = _unitElem (_rawMonoidData monoidData)
    indent = ("  " ++)

prettyElems :: (Show a) => V.Vector a -> [String]
prettyElems env = [ show i ++ " = " ++ show f_ | (i, f_) <- V.toList (V.indexed env) ]

prettyArray :: (Ix i, Ix j, Show i, Show j, Show a) => Array (i,j) a -> [String]
prettyArray table = formatTable $ headerRow : map row xs
  where
    ((xLo, yLo), (xHi, yHi)) = Array.bounds table
    xs = range (xLo, xHi)
    ys = range (yLo, yHi)
    headerRow = "" : map show ys
    row x = show x : [ show (table ! (x,y)) | y <- ys]

formatTable :: [[String]] -> [String]
formatTable cells = addHRule $ renderRow <$> cells
  where
    cellSizes = foldr (zipWith max) (repeat 0) [ length <$> row | row <- cells ]
    renderRow row = addVRule $ zipWith renderCell cellSizes row
    renderCell n cellStr = replicate (n - length cellStr) ' ' ++ cellStr ++ " "
    addVRule [] = []
    addVRule (headerCell : rest) = headerCell ++ "| " ++ concat rest
    addHRule [] = []
    addHRule (headerRow : rest) = headerRow : map hrule headerRow : rest
    hrule '|' = '+'
    hrule _ = '-'

makeEnv :: (Transparent a) => (a -> Int) -> (V.Vector a, Signature)
makeEnv f = (keys, sigs)
  where
    (keys, sigs) = V.unzip $ V.fromList $ sortOn snd [(a, f a) | a <- enum]

fakeEnv :: [Int] -> Signature
fakeEnv ns = V.fromList (sort ns)

-- * RawMonoidData

data RawMonoidData = RawMonoidData {
  _monoidSize :: Int,
  _unitElem :: Int,
  _multTable :: Array (Int,Int) Int
  }
  deriving Show

prettyRawMonoidData :: String -> RawMonoidData -> [String]
prettyRawMonoidData monName raw =
  [monName ++ " = RawMonoid{"] ++
  map ("  " ++) (
    [ "Elements: [0 .. " ++ show n ++ " - 1]" ] ++
    [ "Unit element: " ++ show (_unitElem raw) ] ++
    [ "Multiplication table: " ] ++
    map indent (prettyArray (_multTable raw))
  ) ++
  ["}"]
  where
    n = _monoidSize raw
    indent = ("  " ++)

-- generation

type Signature = V.Vector Int

countZeroes :: Signature -> Int
countZeroes = length . takeWhile (== 0) . V.toList

genRawMonoids :: Signature -> [RawMonoidData]
genRawMonoids sig = do
  let n = V.length sig
  e <- unitCandidates
  let mults = mapMaybe (multMapToArray n) (gen n e)
  mult <- upToIso sig e mults
  pure (RawMonoidData n e mult)
  where
    lengths = V.toList sig
    unitCandidates = [x | (x, lenX', lenX) <- zip3 [0 ..] (-1 : lengths) lengths, lenX' < lenX]

genRawMonoidsForApplicative :: Signature -> [RawMonoidData]
genRawMonoidsForApplicative sig = do
  let n = V.length sig
  e <- unitCandidates
  let mults = mapMaybe (multMapToArray n) (genForApplicative n (countZeroes sig) e)
  mult <- upToIso sig e mults
  pure (RawMonoidData n e mult)
  where
    lengths = V.toList sig
    unitCandidates
      | null sig       = []
      | all (== 0) sig = [0]
      | otherwise      = [x | (x, lenX', lenX) <- zip3 [0 ..] (-1 : lengths) lengths, lenX' < lenX]

genRawMonoidsForMonad :: Signature -> [RawMonoidData]
genRawMonoidsForMonad sig = do
  let n = V.length sig
  e <- unitCandidates
  let mults = mapMaybe (multMapToArray n) (genForMonad n (countZeroes sig) e)
  mult <- upToIso sig e mults
  pure (RawMonoidData n e mult)
  where
    lengths = V.toList sig
    unitCandidates = [x | (x, lenX', lenX) <- zip3 [0 ..] (0 : lengths) lengths, lenX' < lenX]

unitArray :: Ix i => (i,i) -> Array i ()
unitArray bound = Array.accumArray const () bound []

multMapToArray :: Int -> MultTable -> Maybe (Array (Int,Int) Int)
multMapToArray n multMap = itraverse (\ij _ -> Map.lookup ij multMap) $ unitArray ((0,0), (n - 1, n - 1))

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

enter :: MultTable -> KnownEq -> Blocker -> [(MultTable, [KnownEq], Blocker)]
enter table (KnownEq x y z) (Blocker m) =
    case Map.lookup (x,y) m of
        Nothing -> [(table', [], Blocker m)]
        Just eqs -> case checkEquations table' eqs of
            Nothing -> []
            Just (newEqs, newBlockers) ->
                [(table', newEqs, newBlockers <> Blocker (Map.delete (x,y) m))]
    where
        table' = Map.insert (x,y) z table

gen :: Int -> Int -> [MultTable]
gen n e = genTable n e initialTable guess
  where
    xs = [0 .. n - 1]
    initialTable =
      Map.fromList $
             [ ((e, x), x) | x <- xs]
          ++ [ ((x, e), x) | x <- xs]
    guess _ _ = xs

genForApplicative :: Int -> Int -> Int -> [MultTable]
genForApplicative n numZeroes e = genTable n e initialTable guess
  where
    xs = [0 .. n - 1]
    zeroes = [0 .. numZeroes - 1]
    initialTable =
      Map.fromList $
             [ ((e, x), x) | x <- xs]
          ++ [ ((x, e), x) | x <- xs]
    guess x y
      | x < numZeroes || y < numZeroes = zeroes
      | otherwise = xs

genForMonad :: Int -> Int -> Int -> [MultTable]
genForMonad n numZeroes e = genTable n e initialTable guess
  where
    xs = [0 .. n - 1]
    zeroes = [0 .. numZeroes - 1]
    nonzeroes = filter (/= e) [numZeroes .. n - 1]
    initialTable =
      Map.fromList $
        [ ((z, y), z) | z <- zeroes, y <- xs]
          ++ [ ((e, x), x) | x <- xs]
          ++ [ ((x, e), x) | x <- nonzeroes]
    
    guess _ y = if y < numZeroes then zeroes else xs

genTable :: Int -> Int -> MultTable -> (Int -> Int -> [Int]) -> [MultTable]
genTable n e initialTable guess = go initialTable initialEqn initialBlocker
  where
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
    
    nonUnits = filter (/= e) [0 .. n - 1]

    allAssocEq = AssocEq <$> nonUnits <*> nonUnits <*> nonUnits
    (initialEqn, initialBlocker) = case checkEquations initialTable allAssocEq of
        Nothing -> error "Bad initial table?"
        Just updates -> updates

upToIso :: Signature -> Int -> [Array (Int,Int) Int] -> [Array (Int,Int) Int]
upToIso env e tabs = runEquivM id min $ do
  for_ tabs $ \mm -> do
    equate mm mm
  for_ (isoGenerators env e) $ \tr ->
    for_ tabs $ \mm -> equate mm (applyTranspose n tr mm)
  classes >>= traverse desc
  where
    n = V.length env

data Transposition = Transpose Int Int
  deriving (Show)

isoGenerators :: Signature -> Int -> [Transposition]
isoGenerators sig e =
  [Transpose i j | ((i, n), (j, m)) <- zip lengths' (drop 1 lengths'), n == m]
  where
    lengths = V.toList $ V.indexed sig
    lengths' = filter ((/= e) . fst) lengths

applyTranspose :: Int -> Transposition -> Array (Int,Int) Int -> Array (Int,Int) Int
applyTranspose n (Transpose a b) table =
  Array.array ((0,0), (n - 1, n - 1))
    [ ((tr x, tr y), tr z) | ((x,y),z) <- Array.assocs table ]
  where
    tr i
      | i == a = b
      | i == b = a
      | otherwise = i
