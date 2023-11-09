{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module MonadGen
  ( checkLeftUnit,
    checkRightUnit,
    checkAssoc,
    allPures,
    gen,
    GenState (..),
    debugPrint,
    Join,
    Blockade,
  )
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Either.Validation
import Data.Foldable
import qualified Data.LazyVec as Vec
import qualified Data.Map as Map
import Data.Ord (comparing)
import Data.PTraversable
import Data.PTraversable.Extra
import GHC.Generics ((:.:) (..))
import qualified NatMap as NM
import Set1 (Key (), key)
import qualified Set1 as S1

-- Monad properties

checkLeftUnit ::
  (PTraversable m, Eq b) =>
  (forall a. a -> m a) ->
  (forall a. m (m a) -> m a) ->
  m b ->
  Bool
checkLeftUnit pure' join' mb = join' (pure' mb) `eqDefault` mb

checkRightUnit ::
  (PTraversable m, Eq b) =>
  (forall a. a -> m a) ->
  (forall a. m (m a) -> m a) ->
  m b ->
  Bool
checkRightUnit pure' join' mb = join' (fmap pure' mb) `eqDefault` mb

checkAssoc ::
  (PTraversable m, Eq b) =>
  (forall a. m (m a) -> m a) ->
  m (m (m b)) ->
  Bool
checkAssoc join' mmmb = join' (join' mmmb) `eqDefault` join' (fmap join' mmmb)

-- Utilities

allPures :: forall f a. (PTraversable f) => Vec (a -> f a)
allPures = fmap (\f1 -> (<$ f1)) (enum1 @f (Vec.singleton ()))

(!) :: Vec a -> Int -> a
(!) = (Vec.!)

-- Generation

type Gen f = ReaderT (Env f) (StateT (GenState f) [])

data Env f = Env
  { _pure :: forall a. a -> f a,
    _f1 :: Vec (f Int),
    _f2 :: Vec (f (f Int)),
    _f3 :: Vec (f (f (f Int)))
  }

type Join f = NM.NatMap (f :.: f) f

type JoinKey f = Key (f :.: f)

type Blockade f = Rel (JoinKey f) (f :.: f :.: f)

type Rel k f = Map.Map k (S1.Set1 f)

singletonRel :: k -> Key f -> Rel k f
singletonRel k fKey = Map.singleton k (S1.singleton fKey)

unionRel :: (Ord k) => Rel k f -> Rel k f -> Rel k f
unionRel = Map.unionWith S1.union

popRel :: (Ord k) => k -> Rel k f -> (S1.Set1 f, Rel k f)
popRel k m = case Map.lookup k m of
  Nothing -> (S1.empty, m)
  Just s -> (s, Map.delete k m)

mostRelated :: (Ord k) => Rel k f -> Maybe k
mostRelated m
  | Map.null m = Nothing
  | otherwise = Just kTop
  where
    (kTop, _) = maximumBy (comparing (S1.size . snd)) $ Map.toList m

data GenState f = GenState
  { _join :: Join f,
    _blockade :: Blockade f
  }

debugPrint ::
  (PTraversable f, forall a. (Show a) => Show (f a)) =>
  GenState f ->
  IO ()
debugPrint st = do
  putStrLn "----- join ------"
  putStrLn (NM.debug (_join st))
  putStrLn "----- blockade --"
  putStrLn $ "#blockade = " ++ show (Map.size (_blockade st))
  putStrLn "-----------------"
  NM.toTotal
    (_join st)
    (putStrLn "Not completed yet")
    $ \join' ->
      let join'' = join' . Comp1
          assoc = flip all skolem3 $ checkAssoc join''
       in unless assoc (fail "!?!?")

-- (>>=) on Validation
validatedThen :: Validation e a -> (a -> Validation e b) -> Validation e b
validatedThen ea k = case ea of
  Failure e -> Failure e
  Success a -> k a

applyB :: (PTraversable f) => Join f -> f (f a) -> Validation [JoinKey f] (f a)
applyB m ffa = maybe (Failure [k]) Success $ NM.lookup (Comp1 ffa) m
  where
    k = key (Comp1 ffa)

leftAssocB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [JoinKey f] (f a)
leftAssocB m fffa = applyB m fffa `validatedThen` \ffa -> applyB m ffa

rightAssocB :: (PTraversable f) => Join f -> f (f (f a)) -> Validation [JoinKey f] (f a)
rightAssocB m fffa =
  traverseDefault (applyB m) fffa `validatedThen` \ffa -> applyB m ffa

associativity :: (PTraversable f) => Join f -> f (f (f Int)) -> Maybe [JoinKey f]
associativity m fffa =
  case (,) <$> leftAssocB m fffa <*> rightAssocB m fffa of
    Success (leftFa, rightFa) -> if eqDefault leftFa rightFa then Just [] else Nothing
    Failure blockades -> Just blockades

choose :: (Foldable t) => t a -> Gen f a
choose = lift . lift . toList

runGen :: forall f r. (PTraversable f) => (forall a. a -> f a) -> Gen f r -> [(r, GenState f)]
runGen pure' mr = runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env =
      Env
        { _pure = pure',
          _f1 = cache skolem,
          _f2 = cache skolem2,
          _f3 = cache skolem3
        }

    f3 = _f3 env
    k3 = Vec.vec [minBound .. maxBound] :: Vec (Key (f :.: f :.: f))

    join0 = NM.empty
    blockade = maybe (error "should never happen?") (foldl' unionRel Map.empty) $ traverse newConstraint (Vec.zip f3 k3)
    newConstraint (fa, k) = foldMap (\blockKey -> Map.singleton blockKey (S1.singleton k)) <$> associativity join0 fa

    state0 :: GenState f
    state0 =
      GenState
        { _join = join0,
          _blockade = blockade
        }

use :: (Functor f) => f Int -> Vec a -> f a
use template as = (as !) <$> template

entry ::
  forall f.
  (forall a. (Show a) => Show (f a), PTraversable f) =>
  (f :.: f) Int ->
  f Int ->
  Gen f ()
entry lhs rhs =
  do
    join1 <- gets _join
    case NM.lookup lhs join1 of
      Nothing -> return ()
      Just rhs' -> guard (eqDefault rhs rhs')
    let lhsKey = key lhs
        join2 = NM.insert (use rhs) lhsKey join1

    f3 <- asks _f3
    blockade <- gets _blockade

    -- update assocL
    let (blockedAssocs, blockade') = popRel lhsKey blockade
        newConstraint k3 = foldMap (\nextLhsKey -> singletonRel nextLhsKey k3) <$> associativity join2 fa
          where
            fa = f3 Vec.! fromEnum k3
    blockade'' <- case traverse newConstraint (S1.toList blockedAssocs) of
      Nothing -> mzero
      Just newBlockades -> pure $ foldl' unionRel blockade' newBlockades

    modify $ \s ->
      s
        { _join = join2,
          _blockade = blockade''
        }

entryUU :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Gen f ()
entryUU = do
  env <- ask
  let f1 = _f1 env
      u = _pure env
      ui = f1 ! fromEnum (key (u ()))
      uj = fmap (\i -> _length ui * i + i) ui
  entry (Comp1 (u ui)) uj

entryFUG :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => Gen f ()
entryFUG = do
  env <- ask
  let f1 = _f1 env
      u = _pure env
      targets =
        [ fi | (i, fi) <- Vec.toList (Vec.indexed f1), i /= fromEnum (key (u ()))
        ]

      n = _length (u ())
      makeJuf :: f Int -> [f Int]
      makeJuf fi = traverseDefault select fi
        where
          m = _length fi
          select x = [y * m + x | y <- [0 .. n - 1]]
      makeJfu :: f Int -> [f Int]
      makeJfu fi = traverseDefault select fi
        where
          select x = [x * n + y | y <- [0 .. n - 1]]

  for_ targets $ \fi -> do
    juf <- choose $ makeJuf fi
    entry (Comp1 (u fi)) juf
    jfu <- choose $ makeJfu fi
    entry (Comp1 (u <$> fi)) jfu

guess :: forall f. (forall a. (Show a) => Show (f a), PTraversable f) => JoinKey f -> Gen f ()
guess lhsKey = do
  f2 <- asks _f2
  let lhs = Comp1 $ f2 Vec.! fromEnum lhsKey
      lhsVars = toVec lhs
  rhs <- choose (enum1 lhsVars)
  entry lhs rhs

gen :: (forall a. (Show a) => Show (f a), PTraversable f) => (forall a. a -> f a) -> [GenState f]
gen u = snd <$> runGen u (entryUU >> entryFUG >> loop)
  where
    loop = do
      blockade <- gets _blockade
      case mostRelated blockade of
        Nothing -> pure ()
        Just lhsKey -> guess lhsKey >> loop