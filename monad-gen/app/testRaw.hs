{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where


import Targets (H)

import MonoidGen ( genMonoidsForMonad )
import ApplicativeGen (
    makeApplicativeDict,
    ApplicativeData(..),
    genApplicativeDataFrom
  )
import MonadGen ( genFromApplicative, genRaw )

main :: IO ()
main = do
  putStrLn $ "oldGen : " ++ show (fmap (fmap (length . oldGen)) $ applicatives)
  putStrLn $ "rawGen : " ++ show (fmap (fmap (length . rawGen)) $ applicatives)
  where
    monoids = genMonoidsForMonad @H
    applicatives = genApplicativeDataFrom <$> monoids
    oldGen = genFromApplicative . makeApplicativeDict
    rawGen = genRaw . _rawApplicative