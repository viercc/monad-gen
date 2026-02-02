{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE DataKinds #-}
module Main(main) where

import Type.Reflection
import Data.PTraversable (PTraversable)
import qualified Data.Foldable as F
import Data.Traversable (for)

import MonadData
import MonadGen.CSP

import Targets (type F, type G, type H, type St, type V2)
import Data.Fin ( Fin )
import Isomorphism

genFor :: forall f ->
  (Typeable f, PTraversable f, forall a. Show a => Show (f a)) => IO ()
genFor f = do
  putStrLn $ "==== Monad (" ++ show (typeRep @f) ++ ") ===="
  monads <- genMonad @f
  putStrLn $ "#monads = " ++ show (length monads)
  -- let isos = concat $ makeShapeIsoFactors ++ makePositionIsoFactors
  --     monadsModIso = uniqueByIso isos monads
  -- F.for_ (zip [1 :: Int ..] monadsModIso) $ \(i, monadData) ->
  --   mapM_ putStrLn $
  --     prettyMonadDict ("Monad_" ++ show i) "{}" (makeMonadDict monadData)

main :: IO ()
main = do
  genFor F
  genFor G
  genFor H
  genFor (type (St (Fin 2) V2))