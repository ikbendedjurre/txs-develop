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
import qualified ProcId
import qualified ProcDef
-- import qualified ChanId
import qualified VarId
import BehExprDefs
import ProcIdFactory
import ProcDepTree

import qualified ProcInstUpdates
import PBranchUtils

import qualified LinearizeParallel
-- import qualified LinearizeEnable
-- import qualified LinearizeDisable
-- import qualified LinearizeInterrupt

linearizePBranches :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
linearizePBranches bexpr = do
    procDepTree <- getProcDepTree bexpr
    let orderedProcs = getProcsOrderedByMaxDepth procDepTree
    procInstUpdateMap <- Monad.foldM linearizePBranchesInProc Map.empty orderedProcs
    return (ProcInstUpdates.applyMap procInstUpdateMap bexpr)
-- linearizePBranches

linearizePBranchesInProc :: ProcInstUpdates.ProcInstUpdateMap -> ProcId.ProcId -> IOC.IOC ProcInstUpdates.ProcInstUpdateMap
linearizePBranchesInProc procInstUpdateMap pid = do
    IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("linearizePBranchesInProc " ++ (Text.unpack (ProcId.name pid))) ]
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls _vidDecls body) -> do
          let pbranches = Set.filter isPBranch (getBranches body)
          rs <- Monad.mapM (linearizePBranch pid) (Set.toList pbranches)
          let _newBExprs = Set.unions (map fst rs)
          let _newVids = concatMap snd rs
          
          -- resolveProcPrefixes pid
          return procInstUpdateMap
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
  where
    getBranches :: TxsDefs.BExpr -> Set.Set TxsDefs.BExpr
    getBranches (TxsDefs.view -> Choice bexprs) = bexprs
    getBranches bexpr = Set.singleton bexpr
-- linearizePBranchesInProc

linearizePBranch :: ProcId.ProcId -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])
linearizePBranch pid currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide cidSet bexpr) -> do (bexprs, vids) <- linearizeNonHidePBranch pid bexpr
                                                return (Set.map (hide cidSet) bexprs, vids)
      _ -> linearizeNonHidePBranch pid currentBExpr
-- linearizePBranch

linearizeNonHidePBranch :: ProcId.ProcId -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])
linearizeNonHidePBranch pid currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Guard g bexpr) -> do
          (b, bs, vids) <- case bexpr of
                             (TxsDefs.view -> Parallel {}) -> LinearizeParallel.linearize pid g bexpr
                             -- (TxsDefs.view -> Enable {}) -> LinearizeEnable.linearize pid g bexpr
                             -- (TxsDefs.view -> Disable {}) -> LinearizeDisable.linearize pid g bexpr
                             -- (TxsDefs.view -> Interrupt {}) -> LinearizeInterrupt.linearize pid g bexpr
                             _ -> error ("No implementation yet for \"" ++ show currentBExpr ++ "\"!")
          return (Set.insert b bs, vids)
      _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
-- linearizeNonHidePBranch





