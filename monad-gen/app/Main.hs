{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Data.Foldable
import qualified Data.LazyVec as Vec
import Data.List (sort)
import Data.PTraversable
import Data.PTraversable.Extra
import Data.Proxy
import GHC.Generics
import MonadLaws
import MonadGen
import qualified NatMap as NM

import Data.Two
import Targets
import Util

------------------------
-- Tests

forAll :: (Foldable t) => t a -> (a -> Bool) -> Bool
forAll = flip all

monadGen ::
  forall f.
  ( forall a. (Ord a) => Ord (f a),
    forall a. (Show a) => Show (f a),
    PTraversable f
  ) =>
  Proxy f ->
  (String -> IO ()) ->
  IO ()
monadGen _ println = for_ (sort genMonadsModuloIso) docResult
  where
    skolemCache :: Vec (f Int)
    skolemCache = cache skolem

    skolem2Cache :: Vec (f (f Int))
    skolem2Cache = cache skolem2

    skolem3Cache :: Vec (f (f (f Int)))
    skolem3Cache = cache skolem3

    validate :: (forall a. a -> f a) -> (forall a. f (f a) -> f a) -> IO ()
    validate pure' join' =
      if and allLaws
        then return ()
        else fail $ "[leftUnit, rightUnit, assoc] = " ++ show allLaws
      where
        leftUnitLaw = forAll skolemCache $ checkLeftUnit pure' join'
        rightUnitLaw = forAll skolemCache $ checkRightUnit pure' join'
        assocLaw = forAll skolem3Cache $ checkAssoc join'
        allLaws = [leftUnitLaw, rightUnitLaw, assocLaw]

    joinArgsCache :: Vec String
    joinArgsCache = cache $ fmap pad strs
      where
        showLen x = let s = show x in (length s, s)
        strs = cache $ showLen <$> skolem2Cache
        maxLen = maximum $ fmap fst strs
        pad (n, s) = "join $ " ++ s ++ replicate (maxLen - n) ' ' ++ " = "

    docResult (MonadData u joinNM) =
      NM.toTotal joinNM (fail failMsg) $ \join' ->
        do
          validate (<$ u) (join' . Comp1)
          println "{"
          println $ indent <> "pure 0 = " <> show (0 <$ u :: f Int)
          let docLine s ffx = indent <> s <> show (join' (Comp1 ffx))
          mapM_ println $
            Vec.zipWith docLine joinArgsCache skolem2Cache
          println "}\n"
      where
        indent = "    "
        failMsg = "Non-total join:" ++ show (u, NM.debug joinNM)

main :: IO ()
main = do
  writeFile' "output/Writer.txt" $ monadGen @((,) Two) Proxy
  writeFile' "output/Maybe.txt" $ monadGen @Maybe Proxy

  writeFile' "output/F.txt" $ monadGen @F Proxy
  writeFile' "output/G.txt" $ monadGen @G Proxy
  writeFile' "output/H.txt" $ monadGen @H Proxy
  writeFile' "output/I.txt" $ monadGen @I Proxy
  writeFile' "output/J.txt" $ monadGen @J Proxy
  writeFile' "output/T.txt" $ monadGen @T Proxy
