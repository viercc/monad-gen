{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module ModelFinder.Solver.Internal where

import Control.Monad (MonadPlus(..))
import Control.Applicative (Alternative)
import Control.Monad.State (StateT(..), MonadTrans(..))
import Data.Bifunctor (Bifunctor(..))

import ModelFinder.Model ( Model(..) )
import qualified Control.Monad.State.Strict as State

data SearchState k a model = SearchState {
    currentModel :: model,
    waitingDefs :: [(k, a)]
  }

newtype SearchM k a model x = SearchM{ unSearchM :: StateT (SearchState k a model) [] x }
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)

runSearchM :: model -> SearchM k a model x -> [(x, model)]
runSearchM m0 mx = second currentModel <$> runStateT (unSearchM mx) (SearchState m0 [])

choose :: [a] -> SearchM k a model a
choose = SearchM . lift

maybeToSearch :: Maybe x -> SearchM k a model x
maybeToSearch = maybe mzero pure

enterDefsM :: Model k a model => [k] -> a -> SearchM k a model ()
enterDefsM ks a = do
  m <- getsModel
  (m', newDefs) <- maybeToSearch $ enterDef ks a m
  putModel m'
  pushWaitingDefs newDefs

enterEqsM :: Model k a model => [k] -> SearchM k a model ()
enterEqsM ks = do
  m <- getsModel
  (m', newDefs) <- maybeToSearch $ enterEqs ks m
  putModel m'
  pushWaitingDefs newDefs

getsModel :: SearchM k a model model
getsModel = SearchM $ State.gets currentModel

putModel :: model -> SearchM k a model ()
putModel m = SearchM $ State.modify $ \ss -> ss{ currentModel = m }

pushWaitingDefs :: [(k, a)] -> SearchM k a model ()
pushWaitingDefs newDefs = SearchM $ State.modify $ \ss ->
  ss{ waitingDefs = newDefs ++ waitingDefs ss }

-- Gets all waitingDefs and remove them from the state
takeAllWaitingDefs :: SearchM k a model [(k, a)]
takeAllWaitingDefs = SearchM $ State.state $ \ss ->
  (waitingDefs ss, ss{ waitingDefs = [] })
