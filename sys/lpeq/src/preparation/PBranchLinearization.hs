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
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified ProcDef
import qualified SortOf
import qualified VarId
import BehExprDefs
import ProcIdFactory
import ProcDepTree

import qualified ProcInstUpdates

import HideElim
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
    procInstUpdateMap <- Monad.foldM linearizePBranchesInProcWithHide Map.empty orderedProcs
    return (ProcInstUpdates.applyMapToProcInst procInstUpdateMap bexpr)
-- linearizePBranches

linearizePBranchesInProcWithHide :: ProcInstUpdates.ProcInstUpdateMap -> ProcId.ProcId -> IOC.IOC ProcInstUpdates.ProcInstUpdateMap
linearizePBranchesInProcWithHide procInstUpdateMap pid = do
    IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("Linearizing " ++ showProcId pid ++ "...") ]
    (pid', procInstUpdateMap') <- eliminateHide (pid, procInstUpdateMap)
    linearizePBranchesInProc procInstUpdateMap' pid'
-- linearizePBranchesInProcWithHide

linearizePBranchesInProc :: ProcInstUpdates.ProcInstUpdateMap -> ProcId.ProcId -> IOC.IOC ProcInstUpdates.ProcInstUpdateMap
linearizePBranchesInProc procInstUpdateMap pid = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
          -- Function to be used for the instantiation of the linearized process:
          let createProcInst = procInst pid cidDecls
          
          -- Distinguish branches in the body that are finished from branches with parallel structures:
          let (pbranches, npbranches) = Set.partition isPBranch (getBranches body)
          
          -- Linearize branches with parallel structures:
          let tempProcInstUpdateMap = Map.insert pid (ProcInstUpdates.createIdentical pid) procInstUpdateMap
          rs <- Monad.mapM (linearizePBranch createProcInst tempProcInstUpdateMap) (Set.toList pbranches)
          
          -- Check if the result is linear. IT SHOULD BE LINEAR!
          checkLinearBExprs pid (Set.toList pbranches) (Set.toList (Set.unions (map fst rs)))
          
          let newVids = concatMap snd rs
          let newVidDecls = vidDecls ++ newVids
          
          -- Replace process instantiations in branches that were just linearized.
          -- (Currently, they probably are incorrect because they only set newly introduced variables.)
          newProcId <- createFreshProcIdWithDifferentVars pid (map SortOf.sortOf newVidDecls)
          newPBranches <- Set.unions <$> Monad.mapM (ProcInstUpdates.createAndApply pid newProcId newVidDecls) rs
          
          -- Replace instantiations of the current process in branches that were already finished.
          -- Remember how such instantiations should be updated, for later use.
          newProcInstUpdate <- ProcInstUpdates.create newProcId vidDecls newVidDecls Map.empty
          let newProcInstUpdateMap = Map.insert pid newProcInstUpdate procInstUpdateMap
          let newNPBranches = Set.map (ProcInstUpdates.applyMapToBExpr newProcInstUpdateMap) npbranches
          
          -- Register the process with a new body.
          let newBody = choice (Set.union newNPBranches newPBranches)
          registerProc newProcId (ProcDef.ProcDef cidDecls newVidDecls newBody)
          
          return newProcInstUpdateMap
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
-- linearizePBranchesInProc

linearizePBranch :: ([TxsDefs.VExpr] -> TxsDefs.BExpr) -> ProcInstUpdates.ProcInstUpdateMap -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])
linearizePBranch createProcInst procInstUpdateMap currentBExpr =
    let remappedBExpr = ProcInstUpdates.applyMapToBExpr procInstUpdateMap currentBExpr in
      case remappedBExpr of
        (TxsDefs.view -> Hide cidSet bexpr) -> do (bexprs, vids) <- linearizeNonHidePBranch createProcInst bexpr
                                                  return (Set.map (applyHide cidSet) bexprs, vids)
        _ -> linearizeNonHidePBranch createProcInst remappedBExpr
-- linearizePBranch

linearizeNonHidePBranch :: ([TxsDefs.VExpr] -> TxsDefs.BExpr) -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])
linearizeNonHidePBranch createProcInst currentBExpr = do
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





