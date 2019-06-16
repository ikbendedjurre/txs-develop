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

-- import qualified Data.Either as Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
-- import qualified ValExpr
import qualified ProcId
-- import qualified Subst
import qualified ProcDef
-- import qualified ChanId
import qualified VarId
-- import qualified Constant
import BehExprDefs
import ProcIdFactory
import ProcDepTree

import qualified ProcInstUpdates
import PBranchUtils

import qualified LinearizeParallel

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
          _rs <- Monad.mapM linearizePBranch (Set.toList pbranches)
          resolveProcPrefixes pid
          return procInstUpdateMap
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
  where
    getBranches :: TxsDefs.BExpr -> Set.Set TxsDefs.BExpr
    getBranches (TxsDefs.view -> Choice bexprs) = bexprs
    getBranches bexpr = Set.singleton bexpr
-- linearizePBranchesInProc

linearizePBranch :: TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])
linearizePBranch currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Guard g bexpr) -> do
          (b, bs, vids) <- case bexpr of
                             (TxsDefs.view -> Parallel {}) -> LinearizeParallel.linearize g bexpr
                             -- (TxsDefs.view -> Enable {}) ->
                             -- (TxsDefs.view -> Disable {}) ->
                             -- (TxsDefs.view -> Interrupt {}) ->
                             _ -> error ("No implementation yet for \"" ++ show currentBExpr ++ "\"!")
          return (Set.insert b bs, vids)
      _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
-- linearizePBranch

