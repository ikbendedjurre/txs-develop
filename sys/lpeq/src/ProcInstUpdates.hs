{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcInstUpdates
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ProcInstUpdates (
ProcInstUpdate,
ProcInstUpdateMap,
create,
apply,
applyMap,
showItem,
showMap
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified SortOf
import qualified ChanId
import qualified VarId
import BehExprDefs
import ProcIdFactory
import ValFactory

type ProcInstUpdate = (ProcId.ProcId, [Either Int TxsDefs.VExpr])
type ProcInstUpdateMap = Map.Map ProcId.ProcId ProcInstUpdate

showItem :: ProcInstUpdate -> String
showItem (pid, paramUpdates) = Text.unpack (ProcId.name pid) ++ "(" ++ List.intercalate "; " (map showParamUpdate paramUpdates) ++ ")"
  where
    showParamUpdate :: Either Int TxsDefs.VExpr -> String
    showParamUpdate (Left i) = "expr(" ++ show i ++ ")"
    showParamUpdate (Right v) = TxsShow.pshow v
-- showItem

showMap :: ProcInstUpdateMap -> String
showMap m = List.intercalate "\n" (map showEntry (Map.toList m))
  where
    showEntry :: (ProcId.ProcId, ProcInstUpdate) -> String
    showEntry (pid, paramUpdate) = Text.unpack (ProcId.name pid) ++ " -> " ++ showItem paramUpdate
-- showMap

create :: ProcId.ProcId -> [VarId.VarId] -> [VarId.VarId] -> Map.Map VarId.VarId TxsDefs.VExpr -> IOC.IOC ProcInstUpdate
create pid oldVars newVars predefInits = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    pid' <- createFreshProcIdWithDifferentVars pid (map SortOf.sortOf newVars)
    return (pid', map (f tdefs) newVars)
  where
    f :: TxsDefs.TxsDefs -> VarId.VarId -> Either Int TxsDefs.VExpr
    f tdefs vid =
        case List.elemIndex vid oldVars of
          Just i -> Left i
          Nothing -> case predefInits Map.!? vid of
                       Just v -> Right v
                       Nothing -> Right (sort2defaultValue tdefs (SortOf.sortOf vid))
-- create

apply :: ProcInstUpdate -> [ChanId.ChanId] -> [TxsDefs.VExpr] -> TxsDefs.BExpr
apply (pid', paramUpdates) cids vexprs = procInst pid' cids (map f paramUpdates)
  where
    f :: Either Int TxsDefs.VExpr -> TxsDefs.VExpr
    f (Left i) = vexprs !! i
    f (Right v) = v
-- apply

applyMap :: ProcInstUpdates.ProcInstUpdateMap -> TxsDefs.BExpr -> TxsDefs.BExpr
applyMap procInstUpdateMap (TxsDefs.view -> ProcInst pid cids vexprs) =
    case procInstUpdateMap Map.!? pid of
      Just procInstUpdate -> apply procInstUpdate cids vexprs
      Nothing -> error ("Process should have sequential PCs by now (\"" ++ show pid ++ "\"; map = " ++ show procInstUpdateMap ++ ")!")
applyMap _procInstUpdateMap currentBExpr = error ("Process instantiation expected, but found (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")







