{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeApplications#-}
module MonadGen(
  checkLeftUnit,
  checkRightUnit,
  checkAssoc,
  
  allPures,
  gen,
  
  GenState(..),
  debugPrint,
  
  Join,
  KnownAssoc,
  Blockade
) where

import           Data.Foldable
import           GHC.Generics           ((:.:) (..))

import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.PTraversable
import           Data.PTraversable.Extra

import           Data.Either (partitionEithers)
import           Data.List (sortOn)
import qualified Data.Map        as Map
import qualified Data.LazyVec as Vec

import qualified NatMap          as NM
import qualified Set1            as S1
import Set1(Key(), key)

-- Monad properties

checkLeftUnit :: (PTraversable m, Eq b) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m b -> Bool
checkLeftUnit pure' join' mb = join' (pure' mb) `eqDefault` mb

checkRightUnit :: (PTraversable m, Eq b) =>
  (forall a. a -> m a) -> (forall a. m (m a) -> m a) -> m b -> Bool
checkRightUnit pure' join' mb = join' (fmap pure' mb) `eqDefault` mb

checkAssoc :: (PTraversable m, Eq b) =>
  (forall a. m (m a) -> m a) -> m (m (m b)) -> Bool
checkAssoc join' mmmb = join' (join' mmmb) `eqDefault` join' (fmap join' mmmb)

-- Utilities

allPures :: forall f a. (PTraversable f) => Vec (a -> f a)
allPures = fmap (\f1 -> (<$ f1)) (enum1 @f (Vec.singleton ()))

(!) :: Vec a -> Int -> a
(!) = (Vec.!)

-- Generation

type Gen f = ReaderT (Env f) (StateT (GenState f) [])

data Env f =
  Env {
    _pure  :: forall a. a -> f a
  , _f1    :: Vec (f Int)
  , _f2    :: Vec (f (f Int))
  , _f3    :: Vec (f (f (f Int)))
  }

type Join f = NM.NatMap (f :.: f) f
type JoinKey f = Key (f :.: f)
type KnownAssoc f = NM.NatMap (f :.: f :.: f) f
type Blockade f = Map.Map (JoinKey f) (S1.Set1 (f :.: f :.: f))

makeRel :: Ord k => [(k, Key f)] -> Map.Map k (S1.Set1 f)
makeRel = Map.fromListWith S1.union . fmap (fmap S1.singleton)

unionRel :: (Ord k) => Map.Map k (S1.Set1 f) -> Map.Map k (S1.Set1 f) -> Map.Map k (S1.Set1 f)
unionRel = Map.unionWith S1.union

data GenState f =
  GenState {
    _join  :: Join f
  , _assocL :: KnownAssoc f
  , _blockadeL :: Blockade f
  , _assocR :: KnownAssoc f
  , _blockadeR :: Blockade f
  }

debugPrint :: (PTraversable f, forall a. Show a => Show (f a))
           => GenState f -> IO ()
debugPrint st = do
  putStrLn "----- join -----"
  putStrLn (NM.debug (_join st))
  putStrLn "----------------"
  putStrLn $ "#assocL    = " ++ show (NM.size (_assocL st))
  putStrLn $ "#blockadeL = " ++ show (Map.size (_blockadeL st))
  putStrLn $ "#assocR    = " ++ show (NM.size (_assocR st))
  putStrLn $ "#blockadeR = " ++ show (Map.size (_blockadeR st))
  putStrLn "----------------"
  NM.toTotal (_join st)
    (putStrLn "Not completed yet") $ \join' ->
      let join'' = join' . Comp1
          assoc = flip all skolem3 $ checkAssoc join''
      in unless assoc (fail "!?!?")

applyB :: PTraversable f => Join f -> f (f a) -> Either (JoinKey f) (f a)
applyB m ffa = maybe (Left k) Right $ NM.lookup (Comp1 ffa) m
  where k = key (Comp1 ffa)

leftAssocB :: PTraversable f => Join f -> f (f (f a)) -> Either (JoinKey f) (f a)
leftAssocB m fffa =
  do ffa <- applyB m fffa
     applyB m ffa

rightAssocB :: PTraversable f => Join f -> f (f (f a)) -> Either (JoinKey f) (f a)
rightAssocB m fffa =
  do ffa <- traverseDefault (applyB m) fffa
     applyB m ffa

choose :: Foldable t => t a -> Gen f a
choose = lift . lift . toList

runGen :: forall f r. PTraversable f => (forall a. a -> f a) -> Gen f r -> [(r, GenState f)]
runGen pure' mr = runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env = Env {
      _pure = pure',
      _f1 = cache skolem,
      _f2 = cache skolem2,
      _f3 = cache skolem3
    }
    
    f3 = _f3 env
    k3 = [minBound .. maxBound] :: [Key (f :.: f :.: f)]
    
    join0 = NM.empty
    blockadeL =
      makeRel
        [ (j, k)
          | k <- k3
          , Left j <- [leftAssocB join0 (f3 ! fromEnum k)] ]
    blockadeR =
      makeRel
        [ (j, k)
          | k <- k3
          , Left j <- [rightAssocB join0 (f3 ! fromEnum k)] ]
    
    state0 :: GenState f
    state0 = GenState {
      _join = join0
    , _assocL = NM.empty
    , _blockadeL = blockadeL
    , _assocR = NM.empty
    , _blockadeR = blockadeR
    }

use :: Functor f => f Int -> Vec a -> f a
use template as = (as !) <$> template

entry :: forall f. (forall a. Show a => Show (f a), PTraversable f)
      => (f :.: f) Int -> f Int -> Gen f ()
entry lhs rhs =
  do join1 <- gets _join
     case NM.lookup lhs join1 of
       Nothing   -> return ()
       Just rhs' -> guard (eqDefault rhs rhs')
     let join2 = NM.insert (use rhs) (key lhs) join1
     
     f3 <- asks _f3
     assocL <- gets _assocL
     blockadeL <- gets _blockadeL
     assocR <- gets _assocR
     blockadeR <- gets _blockadeR
     
     -- update assocL
     let (newAssocL, blockadeL') = assocUpdates f3 (key lhs) (leftAssocB join2) blockadeL
         assocL' = NM.union assocL newAssocL
     guard $ NM.consistentBy eqDefault newAssocL assocR
     
     -- update assocR
     let (newAssocR, blockadeR') = assocUpdates f3 (key lhs) (rightAssocB join2) blockadeR
         assocR' = NM.union assocR newAssocR
     guard $ NM.consistentBy eqDefault newAssocR assocL'
     
     modify $ \s -> s{
       _join = join2,
       _assocL = assocL',
       _blockadeL = blockadeL',
       _assocR = assocR',
       _blockadeR = blockadeR'
     }

assocUpdates
  :: PTraversable f
  => Vec (f (f (f Int)))
  -> JoinKey f
  -> (f (f (f Int)) -> Either (JoinKey f) (f Int))
  -> Blockade f
  -> (KnownAssoc f, Blockade f)
assocUpdates f3 lhs' jj blockade = (NM.fromList newAssoc, blockade')
  where
    postproc k (Left ffi) = Left (ffi, k)
    postproc k (Right fi) = Right $ NM.makeEntry k (use fi)
    
    (newBlockade, newAssoc) = partitionEithers
        [ postproc k (jj (f3 ! fromEnum k))
        | k <- maybe [] S1.toList (Map.lookup lhs' blockade) ]

    blockade' = unionRel (Map.delete lhs' blockade) (makeRel newBlockade)

entryUU :: forall f. (forall a. Show a => Show (f a), PTraversable f) => Gen f ()
entryUU = do
  env <- ask
  let f1 = _f1 env
      u = _pure env
      ui = f1 ! fromEnum (key (u ()))
      uj = fmap (\i -> _length ui * i + i) ui 
  entry (Comp1 (u ui)) uj

entryFUG :: forall f. (forall a. Show a => Show (f a), PTraversable f) => Gen f ()
entryFUG = do
  env <- ask
  let f1 = _f1 env
      u = _pure env
      targets = [ fi | (i, fi) <- Vec.toList (Vec.indexed f1)
                     , i /= fromEnum (key (u ())) ]
      
      n = _length (u ())
      makeJuf :: f Int -> [f Int]
      makeJuf fi = traverseDefault select fi
        where
          m = _length fi
          select x = [ y * m + x | y <- [0..n - 1] ]
      makeJfu :: f Int -> [f Int]
      makeJfu fi = traverseDefault select fi
        where
          select x = [ x * n + y | y <- [0..n - 1] ]
  
  for_ targets $ \fi -> do
    juf <- choose $ makeJuf fi
    entry (Comp1 (u fi)) juf
    jfu <- choose $ makeJfu fi
    entry (Comp1 (u <$> fi)) jfu

remaining :: PTraversable f => Gen f [(f :.: f) Int]
remaining =
  do f2 <- asks _f2
     join1 <- gets _join
     let notDefined =
           [ ffi' | ffi <- Vec.toList f2
                  , let ffi' = Comp1 ffi
                  , NM.notMember (key ffi') join1 ]
     return (sortOn _length notDefined)

entryAllCombs :: (forall a. Show a => Show (f a), PTraversable f) => (f :.: f) Int -> Gen f ()
entryAllCombs lhs =
  do rhs <- choose $ enum1 (toVec lhs)
     entry lhs rhs

gen :: (forall a. Show a => Show (f a), PTraversable f) => (forall a. a -> f a) -> [GenState f]
gen u = snd <$> runGen u doEverything
  where
    doEverything =
      do entryUU
         entryFUG
         rest <- remaining
         for_ rest entryAllCombs
