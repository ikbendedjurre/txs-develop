{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  PBranchLinearization
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module PBranchLinearization (
linearizePBranches
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified ProcId
import qualified ProcDef
-- import qualified ChanId
import qualified VarId
import BehExprDefs
import ProcIdFactory
import ProcDepTree

import qualified ProcInstUpdates
import BranchUtils
import PBranchUtils

import ProcSearch

import qualified LinearizeParallel
-- import qualified LinearizeEnable
-- import qualified LinearizeDisable
-- import qualified LinearizeInterrupt

linearizePBranches :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
linearizePBranches bexpr = do
    procDepTree <- getProcDepTree bexpr
    let orderedProcs = getProcsOrderedByMaxDepth procDepTree
    procInstUpdateMap <- Monad.foldM linearizePBranchesInProc Map.empty orderedProcs
    return (ProcInstUpdates.applyMapToProcInst procInstUpdateMap bexpr)
-- linearizePBranches

linearizePBranchesInProc :: ProcInstUpdates.ProcInstUpdateMap -> ProcId.ProcId -> IOC.IOC ProcInstUpdates.ProcInstUpdateMap
linearizePBranchesInProc procInstUpdateMap pid = do
    IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("linearizePBranchesInProc " ++ (Text.unpack (ProcId.name pid))) ]
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
          let createProcInst = procInst pid cidDecls
          
          -- Distinguish branches in the body that are finished from branches with parallel structures:
          let tm = Map.insert pid (ProcInstUpdates.createIdentical pid) procInstUpdateMap
          let branches = getBranches (ProcInstUpdates.applyMapToBExpr tm body)
          let (pbranches, npbranches) = Set.partition isPBranch branches
          
          -- Linearize branches with parallel structures:
          rs <- Monad.mapM (linearizePBranch createProcInst) (Set.toList pbranches)
          let newPBranches = Set.unions (map fst rs)
          let newVids = concatMap snd rs
          let newVidDecls = vidDecls ++ newVids
          
          -- Replace process instantiations in branches that were already finished.
          -- Also keep track of this replacement, for later use.
          newProcInstUpdate <- ProcInstUpdates.createWithFreshPid pid vidDecls newVidDecls Map.empty
          let newProcInstUpdateMap' = Map.insert pid newProcInstUpdate procInstUpdateMap
          let npbranches' = Set.map (ProcInstUpdates.applyMapToBExpr newProcInstUpdateMap') npbranches
          
          let bla = choice (Set.union npbranches' newPBranches)
          registerProc (fst newProcInstUpdate) (ProcDef.ProcDef cidDecls newVidDecls bla)
          printProcsInBExpr (procInst (fst newProcInstUpdate) cidDecls (map ValExpr.cstrVar newVidDecls))
          
          -- Replace process instantiations in branches that were just linearized.
          -- (Currently, they probably are incorrect because they only set newly introduced variables.)
          tempUpdate <- ProcInstUpdates.create (fst newProcInstUpdate) newVids newVidDecls Map.empty
          let tempMap = Map.singleton pid tempUpdate
          let newPBranches' = Set.map (ProcInstUpdates.applyMapToBExpr tempMap) newPBranches
          
          -- Register the process with a new body.
          let body' = choice (Set.union npbranches' newPBranches')
          registerProc (fst newProcInstUpdate) (ProcDef.ProcDef cidDecls newVidDecls body')
          
          printProcsInBExpr (procInst (fst newProcInstUpdate) cidDecls (map ValExpr.cstrVar newVidDecls))
          
          -- resolveProcPrefixes pid
          return newProcInstUpdateMap'
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
-- linearizePBranchesInProc

linearizePBranch :: ([TxsDefs.VExpr] -> TxsDefs.BExpr) -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])
linearizePBranch createProcInst currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide cidSet bexpr) -> do (bexprs, vids) <- linearizeNonHidePBranch createProcInst bexpr
                                                return (Set.map (applyHide cidSet) bexprs, vids)
      _ -> linearizeNonHidePBranch createProcInst currentBExpr
-- linearizePBranch

linearizeNonHidePBranch :: ([TxsDefs.VExpr] -> TxsDefs.BExpr) -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])
linearizeNonHidePBranch createProcInst currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Guard g bexpr) -> do
          case bexpr of
            (TxsDefs.view -> Parallel {}) -> LinearizeParallel.linearize createProcInst g bexpr
            -- (TxsDefs.view -> Enable {}) -> LinearizeEnable.linearize pid g bexpr
            -- (TxsDefs.view -> Disable {}) -> LinearizeDisable.linearize pid g bexpr
            -- (TxsDefs.view -> Interrupt {}) -> LinearizeInterrupt.linearize pid g bexpr
            _ -> error ("No implementation yet for \"" ++ show currentBExpr ++ "\"!")
      _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
-- linearizeNonHidePBranch





