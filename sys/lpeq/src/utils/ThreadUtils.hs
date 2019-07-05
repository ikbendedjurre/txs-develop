{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ThreadUtils
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module ThreadUtils (
BranchData(..),
getBranchData,
ThreadData(..),
getThreadData,
filterThreadData,
partitionThreadData
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ChanId
import qualified VarId
import ActOfferFactory
import VarFactory
import BehExprDefs

import BranchLinearityUtils

data BranchData = BranchData { bOrigExpr :: TxsDefs.BExpr
                             , bHidChans :: Set.Set ChanId.ChanId
                             , bVizChans :: Set.Set ChanId.ChanId
                             , bActOffer :: ActOffer
                             , bParamEqs :: Map.Map VarId.VarId TxsDefs.VExpr
                             , bOfferVarsPerChan :: Map.Map ChanId.ChanId [VarId.VarId]
                             } deriving (Eq, Ord, Show)
-- BranchData

getBranchData :: TxsDefs.BExpr -> IOC.IOC BranchData
getBranchData bexpr = do
    let (hiddenChans, actOffer, recProcInst) = getBranchSegments bexpr
    (_branches, paramEqs) <- extractProcInstData recProcInst
    let offerVarsPerChan = getOfferVarsPerChan actOffer
    return (BranchData { bOrigExpr = bexpr
                       , bHidChans = hiddenChans
                       , bVizChans = getActOfferChans actOffer
                       , bActOffer = actOffer
                       , bParamEqs = Map.fromList paramEqs
                       , bOfferVarsPerChan = offerVarsPerChan
                       })
-- getBranchData

data ThreadData = ThreadData { tBranchData :: Set.Set BranchData            -- (Data about the) branches of the thread to which the ProcInst refers.
                             , tInitFlag :: VarId.VarId                     -- Flag that indicates whether the thread has been initialized.
                             , tInitEqs :: [(VarId.VarId, TxsDefs.VExpr)]   -- Equations with which the thread should be initialized.
                             } deriving (Eq, Ord, Show)
-- ThreadData

-- Extracts data from a thread (which must have the form of a process instantiation).
-- Also creates an initialization flag for the thread.
getThreadData :: TxsDefs.BExpr -> IOC.IOC ThreadData
getThreadData bexpr = do
    (branches, initEqs) <- extractProcInstData bexpr
    branchData <- Set.fromList <$> Monad.mapM getBranchData (Set.toList branches)
    initFlag <- createFreshBoolVarFromPrefix "initFlag"
    return (ThreadData { tBranchData = branchData, tInitFlag = initFlag, tInitEqs = initEqs })
-- getThreadData

filterThreadData :: (Set.Set ChanId.ChanId -> Bool) -> ThreadData -> ThreadData
filterThreadData restrictionFunction threadData =
    threadData { tBranchData = Set.filter (restrictionFunction . bVizChans) (tBranchData threadData) }
-- filterThreadData

partitionThreadData :: (Set.Set ChanId.ChanId -> Bool) -> ThreadData -> (ThreadData, ThreadData)
partitionThreadData restrictionFunction threadData =
    let (p, q) = Set.partition (restrictionFunction . bVizChans) (tBranchData threadData) in
      (threadData { tBranchData = p }, threadData { tBranchData = q })
-- partitionThreadData


