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
createWithFreshPid,
createIdentical,
showItem,
showMap,
apply,
applyMapToProcInst,
applyMapToBExpr
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
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
create newPid oldVars newVars predefInits = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    return (newPid, map (f tdefs) newVars)
  where
    f :: TxsDefs.TxsDefs -> VarId.VarId -> Either Int TxsDefs.VExpr
    f tdefs vid =
        case List.elemIndex vid oldVars of
          Just i -> Left i
          Nothing -> case predefInits Map.!? vid of
                       Just v -> Right v
                       Nothing -> Right (sort2defaultValue tdefs (SortOf.sortOf vid))
-- create

createWithFreshPid :: ProcId.ProcId -> [VarId.VarId] -> [VarId.VarId] -> Map.Map VarId.VarId TxsDefs.VExpr -> IOC.IOC ProcInstUpdate
createWithFreshPid oldPid oldVars newVars predefInits = do
    newPid <- createFreshProcIdWithDifferentVars oldPid (map SortOf.sortOf newVars)
    create newPid oldVars newVars predefInits
-- createWithFreshPid

createIdentical :: ProcId.ProcId -> ProcInstUpdate
createIdentical pid = (pid, map Left [0..length (ProcId.procvars pid) - 1])

apply :: ProcInstUpdate -> [ChanId.ChanId] -> [TxsDefs.VExpr] -> TxsDefs.BExpr
apply (newPid, paramUpdates) cids vexprs = procInst newPid cids (map f paramUpdates)
  where
    f :: Either Int TxsDefs.VExpr -> TxsDefs.VExpr
    f (Left i) = vexprs !! i
    f (Right v) = v
-- apply

applyMapToProcInst :: ProcInstUpdates.ProcInstUpdateMap -> TxsDefs.BExpr -> TxsDefs.BExpr
applyMapToProcInst procInstUpdateMap (TxsDefs.view -> ProcInst pid cids vexprs) =
    case procInstUpdateMap Map.!? pid of
      Just procInstUpdate -> apply procInstUpdate cids vexprs
      Nothing -> error ("Process not found in map (\"" ++ show pid ++ "\"; map = " ++ showMap procInstUpdateMap ++ ")!")
applyMapToProcInst _procInstUpdateMap currentBExpr = error ("Process instantiation expected, but found (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

applyMapToBExpr :: ProcInstUpdates.ProcInstUpdateMap -> TxsDefs.BExpr -> TxsDefs.BExpr
applyMapToBExpr procInstUpdateMap currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> ProcInst {}) ->
          applyMapToProcInst procInstUpdateMap currentBExpr
      (TxsDefs.view -> Guard g bexpr) ->
          guard g (applyMapToBExpr procInstUpdateMap bexpr)
      (TxsDefs.view -> Choice bexprs) ->
          choice (Set.map (applyMapToBExpr procInstUpdateMap) bexprs)
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          parallel cidSet (map (applyMapToBExpr procInstUpdateMap) bexprs)
      (TxsDefs.view -> Hide cidSet bexpr) ->
          hide cidSet (applyMapToBExpr procInstUpdateMap bexpr)
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          enable (applyMapToBExpr procInstUpdateMap bexpr1) acceptOffers (applyMapToBExpr procInstUpdateMap bexpr2)
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          disable (applyMapToBExpr procInstUpdateMap bexpr1) (applyMapToBExpr procInstUpdateMap bexpr2)
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          interrupt (applyMapToBExpr procInstUpdateMap bexpr1) (applyMapToBExpr procInstUpdateMap bexpr2)
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          actionPref actOffer (applyMapToBExpr procInstUpdateMap bexpr)
      (TxsDefs.view -> ValueEnv _venv _bexpr) ->
          error ("ValueEnv should have been eliminated by now (\"" ++ show currentBExpr ++ "\")!")
      (TxsDefs.view -> StAut _sid _venv _transitions) ->
          error ("StAut should have been eliminated by now (\"" ++ show currentBExpr ++ "\")!")
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- applyMapToBExpr





