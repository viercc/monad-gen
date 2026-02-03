{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main(main) where

import Type.Reflection
import Data.PTraversable (PTraversable)
import qualified Data.Foldable as F

import MonadData
import MonadGen.CSP

import Targets (type F, type G, type H, type I, type St, type V2)
import Data.Fin ( Fin )
import Isomorphism
import System.IO
import System.Exit (exitFailure)
import Data.PTraversable.Extra (skolem3, skolem)
import MonadLaws

genFor :: forall f ->
  (Typeable f, PTraversable f, forall a. Show a => Show (f a)) => IO ()
genFor f = do
  putStrLn $ "==== Monad (" ++ show (typeRep @f) ++ ") ===="
  monads <- genMonad @f
  putStrLn $ "#monads = " ++ show (length monads)
  let isos = concat $ makeShapeIsoFactors ++ makePositionIsoFactors
      monadsModIso = uniqueByIso isos monads
  putStrLn $ "#monadsModIso = " ++ show (length monadsModIso)
  F.for_ (zip [1 :: Int ..] monadsModIso) $ \(i, monadData) -> do
    let dict = makeMonadDict monadData
    validateMonadDict dict
    mapM_ putStrLn $
      prettyMonadDict ("Monad_" ++ show i) "{}" dict

validateMonadDict :: forall f.
     (PTraversable f, forall a. Show a => Show (f a))
  => MonadDict f -> IO ()
validateMonadDict MonadDict{ _monadPure = pure', _monadJoin = join' }
   = if null allFails
       then pure ()
       else do
        putErr "!Monad law failure"
        mapM_ putErr allFails
        exitFailure
  where
    putErr = hPutStrLn stderr

    skolemCache :: [f Int]
    skolemCache = F.toList skolem

    skolem3Cache :: [f (f (f Int))]
    skolem3Cache = F.toList skolem3
 
    leftUnitFails = 
      [ "leftUnit " ++ show fx | fx <- skolemCache, not (checkLeftUnit pure' join' fx) ]
    rightUnitFails = 
      [ "rightUnit " ++ show fx | fx <- skolemCache, not (checkRightUnit pure' join' fx) ]
    assocFails = 
      [ "assoc " ++ show fffx | fffx <- skolem3Cache, not (checkAssoc join' fffx) ]

    allFails = leftUnitFails ++ rightUnitFails ++ assocFails


main :: IO ()
main = do
  genFor F
  genFor G
  genFor H
  -- genFor I
  genFor (type (St (Fin 2) V2))
  genFor (type (St (Fin 3) V2))
