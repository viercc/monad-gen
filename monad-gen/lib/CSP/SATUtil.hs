{-# LANGUAGE RankNTypes #-}
module CSP.SATUtil(
  debug, printStat,
  runIterative,

  Lit'(..),
  Clause(..),
  Prop(..),
  false, true, lit', clause',
  (/\), andProp, (\/),

  addProp, addClause, addClause'
) where

import Data.Foldable (for_)

import Control.Monad.SAT (SAT, Neg (..), Lit)
import qualified Control.Monad.SAT as SAT

import Data.IORef
import Control.Monad.IO.Class (liftIO)

debug :: String -> SAT s ()
-- debug = liftIO . putStrLn
debug = const (pure ())

printStat :: SAT s ()
printStat = do
  statNumberOfVars <- SAT.numberOfVariables
  statNumberOfClauses <- SAT.numberOfClauses
  liftIO . putStrLn $ "INFO: SAT stats (vars, clauses) = "
    ++ show (statNumberOfVars, statNumberOfClauses)

runIterative :: forall a. (forall s. SAT s (SAT s a, a -> SAT s ())) -> IO [a]
runIterative generator =
  do results <- newIORef []
     let body :: forall s'. SAT s' ()
         body = do
           (nextSolution, exclude) <- generator
           let loop = do
                a <- nextSolution
                liftIO $ modifyIORef' results (a:)
                exclude a
                loop
           loop
     _ <- SAT.runSATMaybe body
     readIORef results

-- | Literal or constant
data Lit' s = LitFalse | LitHit (Lit s) | LitTrue

instance Neg (Lit' s) where
  neg LitFalse = LitTrue
  neg (LitHit l) = LitHit (neg l)
  neg LitTrue = LitFalse

newtype Clause s = Clause [Lit s]
newtype Prop s = Prop [Clause s]

false, true :: Prop s
false = Prop [Clause []]
true = Prop []

lit :: Lit s -> Prop s
lit l = Prop [Clause [l]]

lit' :: Lit' s -> Prop s
lit' l' = case l' of
  LitFalse -> false
  LitHit l -> lit l
  LitTrue -> true

clause' :: [Lit' s] -> Prop s
clause' = foldr ((\/) . lit') false

(/\) :: Prop s -> Prop s -> Prop s
Prop cs1 /\ Prop cs2 = Prop (cs1 ++ cs2)

(\/) :: Prop s -> Prop s -> Prop s
Prop cs \/ Prop ds = Prop [ Clause (c ++ d) | Clause c <- cs, Clause d <- ds]

andProp :: [Prop s] -> Prop s
andProp = foldr (/\) true

addProp :: Prop s -> SAT s ()
addProp (Prop ps) = for_ ps addClause

addClause :: Clause s -> SAT s ()
addClause (Clause c) = SAT.addClause c

addClause' :: [Lit' s] -> SAT s ()
addClause' = addProp . clause'
