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
import qualified Data.IntSet     as IS
import qualified Data.IntMap     as IM
import qualified Data.LazyVec as Vec
import qualified NatMap                 as NM

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
  , _f2    :: Vec ((f :.: f) Int)
  , _f3    :: Vec ((f :.: f :.: f) Int)
  }

newtype JoinKey f = JoinKey (f (f ()))
  deriving (Eq, Ord) via WrappedPTraversable (f :.: f) ()

type Join f = NM.NatMap (f :.: f) f
type KnownAssoc f = IM.IntMap (f Int)
type Blockade f = Map.Map (JoinKey f) IS.IntSet

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
  putStrLn $ "#assocL    = " ++ show (IM.size (_assocL st))
  putStrLn $ "#blockadeL = " ++ show (Map.size (_blockadeL st))
  putStrLn $ "#assocR    = " ++ show (IM.size (_assocR st))
  putStrLn $ "#blockadeR = " ++ show (Map.size (_blockadeR st))
  putStrLn "----------------"
  NM.toTotal (_join st)
    (putStrLn "Not completed yet") $ \join' ->
      let join'' = join' . Comp1
          assoc = flip all skolem3 $ checkAssoc join''
      in unless assoc (fail "!?!?")

applyB :: PTraversable f => Join f -> (f :.: f) a -> Either (JoinKey f) (f a)
applyB m ffa = maybe (Left ff0) Right $ NM.lookup ffa m
  where ff0 = JoinKey . unComp1 $ void ffa

leftAssocB :: PTraversable f => NM.NatMap (f :.: f) f -> (f :.: f :.: f) a -> Either (JoinKey f) (f a)
leftAssocB m fffa =
  do ffa <- applyB m (Comp1 . fmap unComp1 . unComp1 $ fffa)
     applyB m (Comp1 ffa)

rightAssocB :: PTraversable f => NM.NatMap (f :.: f) f -> (f :.: f :.: f) a -> Either (JoinKey f) (f a)
rightAssocB m fffa =
  do ffa <- traverse (applyB m) (unComp1 fffa)
     applyB m (Comp1 ffa)

runGen :: forall f r. PTraversable f => (forall a. a -> f a) -> Gen f r -> [(r, GenState f)]
runGen pure' mr = runStateT (runReaderT mr env) state0
  where
    env :: Env f
    env = Env {
      _pure = pure',
      _f1 = cache skolem,
      _f2 = cache skolem,
      _f3 = cache skolem
    }
    
    f3 = _f3 env
    
    join0 = NM.empty
    blockadeL =
      Map.fromListWith IS.union
        [ (ff0, IS.singleton k)
          | (k, fffi) <- Vec.toList (Vec.indexed f3)
          , Left ff0 <- [leftAssocB join0 fffi] ]
    blockadeR =
      Map.fromListWith IS.union
        [ (ff0, IS.singleton k)
          | (k, fffi) <- Vec.toList (Vec.indexed f3)
          , Left ff0 <- [rightAssocB join0 fffi] ]
    
    state0 :: GenState f
    state0 = GenState {
      _join = join0
    , _assocL = IM.empty
    , _blockadeL = blockadeL
    , _assocR = IM.empty
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
     let join2 = NM.insertA (use rhs) lhs join1
     
     f3 <- asks _f3
     assocL <- gets _assocL
     blockadeL <- gets _blockadeL
     assocR <- gets _assocR
     blockadeR <- gets _blockadeR
     
     let lhs' = JoinKey . unComp1 $ void lhs
     
     -- update assocL
     let postproc k (Left ffi) = Left (ffi, IS.singleton k)
         postproc k (Right fi) = Right (k, fi)
         (newBlockadeL, newAssocL) = partitionEithers
           [ postproc k (leftAssocB join2 (f3 ! k))
           | k <- maybe [] IS.toList (Map.lookup lhs' blockadeL) ]
         newBlockadeMapL = Map.fromListWith IS.union newBlockadeL
         blockadeL' = Map.unionWith IS.union (Map.delete lhs' blockadeL) newBlockadeMapL
         assocL' = IM.union assocL (IM.fromList newAssocL)
     for_ newAssocL $ \(k, fi) ->
       case IM.lookup k assocR of
         Nothing  -> return ()
         Just fi' -> guard (eqDefault fi fi')
     
     -- update assocR
     let (newBlockadeR, newAssocR) = partitionEithers
           [ postproc k (rightAssocB join2 (f3 ! k))
           | k <- maybe [] IS.toList (Map.lookup lhs' blockadeR) ]
         newBlockadeMapR = Map.fromListWith IS.union newBlockadeR
         blockadeR' = Map.unionWith IS.union (Map.delete lhs' blockadeR) newBlockadeMapR
         assocR' = IM.union assocR (IM.fromList newAssocR)
     for_ newAssocR $ \(k, fi) ->
       case IM.lookup k assocL' of
         Nothing  -> return ()
         Just fi' -> guard (eqDefault fi fi')
     
     modify $ \s -> s{
       _join = join2,
       _assocL = assocL',
       _blockadeL = blockadeL',
       _assocR = assocR',
       _blockadeR = blockadeR'
     }

entryUnitEqs :: (forall a. Show a => Show (f a), PTraversable f) => Gen f ()
entryUnitEqs = do
  env <- ask
  entryUU' (_pure env)
  entryFUG' (_pure env)

entryUU' :: forall f. (forall a. Show a => Show (f a), PTraversable f) => (forall a. a -> f a) -> Gen f ()
entryUU' u = do
  f1 <- asks _f1
  let ui = f1 ! fIdx (u ())
      uj = fmap (\i -> length ui * i + i) ui 
  entry (Comp1 (u ui)) uj

entryFUG' :: forall f. (forall a. Show a => Show (f a), PTraversable f) => (forall a. a -> f a) -> Gen f ()
entryFUG' u = do
  f1 <- asks _f1
  let targets = [ fi | (i, fi) <- Vec.toList (Vec.indexed f1)
                          , i /= fIdx (u ()) ]
  for_ targets $ \fi -> do
    juf <- lift . lift $ makeJuf fi
    entry (Comp1 (u fi)) juf
    jfu <- lift . lift $ makeJfu fi
    entry (Comp1 (u <$> fi)) jfu
  where
    n = length (u ())
    makeJuf :: f Int -> [f Int]
    makeJuf fi = traverse select fi
      where
        m = length fi
        select x = [ y * m + x | y <- [0..n - 1] ]
    makeJfu :: f Int -> [f Int]
    makeJfu fi = traverse select fi
      where
        select x = [ x * n + y | y <- [0..n - 1] ]

remaining :: PTraversable f => Gen f [(f :.: f) Int]
remaining =
  do f2 <- asks _f2
     join1 <- gets _join
     let notDefined =
           [ ffi | ffi <- Vec.toList f2
                 , NM.notMember ffi join1 ]
     return (sortOn length notDefined)

entryAllCombs :: (forall a. Show a => Show (f a), PTraversable f) => (f :.: f) Int -> Gen f ()
entryAllCombs lhs =
  do let args = toVec lhs
     rhs <- lift . lift $ Vec.toList (enum1 args)
     entry lhs rhs

gen :: (forall a. Show a => Show (f a), PTraversable f) => (forall a. a -> f a) -> [GenState f]
gen u = snd <$> runGen u doEverything
  where
    doEverything =
      do entryUnitEqs
         rest <- remaining
         for_ rest entryAllCombs
