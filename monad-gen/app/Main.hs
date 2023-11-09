{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE DerivingVia               #-}
module Main(main) where

import           Data.Foldable
import           Data.Proxy
import           GHC.Generics

import           Data.PTraversable
import           Data.PTraversable.Extra
import qualified Data.LazyVec as Vec
import qualified NatMap                 as NM
import           Targets
import           MonadGen
import           Util

------------------------
-- Tests

forAll :: (Foldable t) => t a -> (a -> Bool) -> Bool
forAll = flip all

monadGen
  :: forall f.
       (forall a. Ord a => Ord (f a),
       forall a. Show a => Show (f a),
       PTraversable f)
       => Proxy f -> (String -> IO ()) -> IO ()
monadGen _ println = for_ genMonadsModuloIso docResult
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
        leftUnitLaw  = forAll skolemCache $ checkLeftUnit pure' join'
        rightUnitLaw = forAll skolemCache $ checkRightUnit pure' join'
        assocLaw     = forAll skolem3Cache $ checkAssoc join'
        allLaws = [leftUnitLaw, rightUnitLaw, assocLaw]
    
    joinArgsCache :: Vec String
    joinArgsCache = cache $ fmap pad strs
      where showLen x = let s = show x in (length s, s)
            strs = cache $ showLen <$> skolem2Cache
            maxLen = maximum $ fmap fst strs
            pad (n, s) = "join $ " ++ s ++ replicate (maxLen - n) ' ' ++ " = "
    
    docResult (MonadData u joinNM) =
      NM.toTotal joinNM (fail failMsg) $ \join' ->
        do validate (<$ u) (join' . Comp1)
           let docLine s ffx = s ++ show (join' (Comp1 ffx))
           println $ replicate 60 '-'
           println $ "pure 0 = " <> show (0 <$ u :: f Int)
           mapM_ println $
             Vec.zipWith docLine joinArgsCache skolem2Cache
           println ""
      where failMsg = "Non-total join:" ++ show (u, NM.debug joinNM)

main :: IO ()
main =
  do writeFile' "monad-gen-F.txt" $ monadGen @F Proxy
     writeFile' "monad-gen-G.txt" $ monadGen @G Proxy
     writeFile' "monad-gen-H.txt" $ monadGen @H Proxy
     writeFile' "monad-gen-W.txt" $ monadGen @W Proxy
     writeFile' "monad-gen-J.txt" $ monadGen @J Proxy
     writeFile' "monad-gen-T.txt" $ monadGen @T Proxy
     -- writeFile' "monad-gen-Y.txt" $ monadGen @Y Proxy
