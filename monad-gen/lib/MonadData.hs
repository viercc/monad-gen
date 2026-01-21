{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}

module MonadData
  (
    MonadDict(..),
    makeMonadDict,

    MonadData(..),
    actIso,
    uniqueByIso,
    groupByIso,

    -- * Read/Write
    serializeMonadDataList,
    deserializeMonadDataList
  )
where

import Control.Monad
import Data.Foldable
import qualified Data.Set as Set
import Data.PTraversable
import Data.PTraversable.Extra
import GHC.Generics ((:.:) (..))
import Data.FunctorShape
import qualified Data.NatMap as NM

import Isomorphism (Iso (..))

import qualified Data.Vector as V
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))
import Text.Read (readMaybe)
import Data.List (sort)
import EquivalenceUtil (uniqueUpTo, groupUpTo)
import Data.Traversable.Extra (indices)

-- Monad dictionary

data MonadData f = MonadData (Shape f) (NM.NatMap (f :.: f) f)

deriving instance (WeakEq f, Eq (f (f Ignored)), Eq (f NM.Var)) => Eq (MonadData f)
deriving instance (WeakOrd f, Ord (f (f Ignored)), Ord (f NM.Var)) => Ord (MonadData f)

signatureOf :: forall f proxy. PTraversable f => proxy f -> [Int]
signatureOf _ = length <$> (shapes :: [f ()])

serializeMonadDataList :: forall f. PTraversable f => [MonadData f] -> [String]
serializeMonadDataList monadData =
  show (signatureOf @f Proxy) : map (show . encodeMonadData) (sort monadData)

deserializeMonadDataList :: forall f. PTraversable f => [String] -> Either String [MonadData f]
deserializeMonadDataList [] = Left "No signature"
deserializeMonadDataList (sigStr : records) =
  do readSig
     traverse parseMonadData (zip [2..] records)
  where
    readSig :: Either String ()
    readSig = case readMaybe sigStr of
      Nothing -> Left "parse error at signature"
      Just sig
        | sig == expectedSig -> Right ()
        | otherwise -> Left "signature mismatch"

    expectedSig :: [Int]
    expectedSig = signatureOf (Proxy :: Proxy f)

    parseMonadData :: (Int, String) -> Either String (MonadData f)
    parseMonadData (lineNo, str) = case readMaybe str of
      Nothing -> Left $ "parse error at line " ++ show lineNo
      Just monadDataRaw -> case decodeMonadData monadDataRaw of
        Nothing -> Left $ "non well-formed MonadData at line " ++ show lineNo
        Just md -> Right md

type MonadCode = (Int, [(Int, [Int])])

encodeMonadData :: forall f. PTraversable f => MonadData f -> MonadCode
encodeMonadData (MonadData pureShape joinNM) = (reindex pureShape, encodeEntry <$> joinEntries)
  where
    fIndex :: Set.Set (Shape f)
    fIndex = Set.fromList (Shape <$> shapes)

    reindex sh = fromMaybe (-1) $ Set.lookupIndex sh fIndex

    joinEntries = [ res | Shape ff1 <- NM.keys joinNM, Just res <- [ NM.lookup (indices ff1) joinNM ] ]
    encodeEntry fn = (reindex (Shape fn), toList fn)

decodeMonadData :: forall f. PTraversable f => MonadCode -> Maybe (MonadData f)
decodeMonadData (pureIdx, joinData) = MonadData <$> mpureShape <*> mjoinNM
  where
    f1 :: V.Vector (f Int)
    f1 = skolem
    f2 :: V.Vector (f (f Int))
    f2 = skolem2

    mpureShape = Shape <$> (f1 V.!? pureIdx)
    mkEntry (ffn, (rhsIndex, rhsVars)) = 
      do rhsSkolem <- f1 V.!? rhsIndex
         guard (length rhsSkolem == length rhsVars)
         let rhs = fmap (rhsVars !!) rhsSkolem
         NM.makeEntry (Comp1 ffn) rhs
    mjoinNM = do
      joinNM <- NM.fromEntries <$> traverse mkEntry (zip (V.toList f2) joinData)
      guard (NM.size joinNM == V.length f2)
      pure joinNM

data MonadDict f =
  MonadDict {
    _monadPure :: forall a. a -> f a,
    _monadJoin :: forall a. f (f a) -> f a
  }

actIso :: PTraversable f => Iso f -> MonadData f -> MonadData f
actIso (Iso g _) (MonadData u joinNM) = MonadData (mapShape g u) joinNM' 
  where
    joinNM' =
      NM.fromEntries $ do
        (ff1, fx) <- NM.getKeyValue <$> NM.toEntries joinNM
        let ffx = NM.indices ff1
        Just e' <- [ NM.makeEntry (Comp1 . g . fmap g . unComp1 $ ffx) (g fx) ]
        pure e'

uniqueByIso :: forall f. (PTraversable f, forall a. (Show a) => Show (f a), forall a. Ord a => Ord (f a))
  => [Iso f] -> [MonadData f] -> [MonadData f]
uniqueByIso isoGenerators = uniqueUpTo (actIso <$> isoGenerators)

groupByIso :: forall f. (PTraversable f, forall a. (Show a) => Show (f a), forall a. Ord a => Ord (f a))
  => [Iso f] -> [MonadData f] -> [[MonadData f]]
groupByIso isoGenerators = groupUpTo (actIso <$> isoGenerators)

makeMonadDict :: (PTraversable f) => MonadData f -> MonadDict f
makeMonadDict (MonadData (Shape u) joinMap) = 
    case NM.toTotal joinMap of
      Nothing -> error "well..."
      Just theJoin -> MonadDict (<$ u) (NM.unwrapNT theJoin . Comp1)
