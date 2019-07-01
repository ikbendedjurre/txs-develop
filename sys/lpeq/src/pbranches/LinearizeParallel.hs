{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LinearizeParallel
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module LinearizeParallel (
linearize
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
-- import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified Subst
import qualified ChanId
import qualified VarId
import ActOfferFactory
import ValFactory
import VarFactory
import BehExprDefs

import PBranchUtils
import UniqueObjects
import LinearizeParallelUtils

-- import ProcSearch

type Info = ( [TxsDefs.VExpr] -> TxsDefs.BExpr    -- Function that should be used to recursively instantiate the parent process.
            , [VarId.VarId]                       -- Flag variables that indicate whether a child process has been initialized.
            , [VarId.VarId]                       -- Extra variables that the parent process will have to add to the process declaration.
            , TxsDefs.VExpr                       -- Guard.
            , Set.Set ChanId.ChanId               -- Channels that are synchronized.
            )
-- Info

linearize :: PBranchLinearizer
linearize createProcInst g (TxsDefs.view -> Parallel synchronizedChans threads) = do
    -- We require that all thread processes are unique, as well as all variables that they declare!
    threads' <- ensureDistinguishableThreads threads
    Monad.mapM_ ensureFreshVarsInProcInst threads'
    
    -- Extract data from all parallel sub-expressions:
    dataPerThread <- Monad.mapM getThreadData threads'
    
    -- List all channel combinations used in the branches;
    -- then partition them into channel combinations that must synchronize and channel combinations that must not.
    let allCidSets = Set.unions (map (Set.map bVizChans . tBranchData) dataPerThread)
    let (syncingCidSets, unsyncedCidSets) = Set.partition (\c -> Set.intersection c synchronizedChans /= Set.empty) allCidSets
    
    -- Channel combinations that must synchronize require that
    -- they synchronize on exactly the same channels:
    let synchronizingChans = foldl Set.intersection synchronizedChans syncingCidSets
    let syncedCidSets = Set.filter (\c -> Set.intersection c synchronizedChans == synchronizingChans) syncingCidSets
    
    let syncedBranchesPerThread = map (filterThreadData syncedCidSets) dataPerThread
    let unsyncedBranchesPerThread = map (filterThreadData unsyncedCidSets) dataPerThread
    
    -- Set variable declarations required by the new branches:
    let initFlags = map tInitFlag dataPerThread
    let newVidDecls = concatMap (map fst . tInitEqs) dataPerThread
    
    -- ...
    let info = (createProcInst, initFlags, newVidDecls, g, synchronizingChans)
    syncedBranches <- synchronizeOneBranchPerThread info syncedBranchesPerThread
    unsyncedBranches <- leaveBranchesUnsynchronized info unsyncedBranchesPerThread
    
    return (Set.union syncedBranches unsyncedBranches, initFlags ++ newVidDecls)
linearize _ _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

-- Considers all lists consisting of one branch per thread.
-- Synchronizes those branches.
synchronizeOneBranchPerThread :: Info -> [ThreadData] -> IOC.IOC (Set.Set TxsDefs.BExpr)
synchronizeOneBranchPerThread info threadData = buildList [] threadData
  where
    buildList :: [(BranchData, ThreadData)] -> [ThreadData] -> IOC.IOC (Set.Set TxsDefs.BExpr)
    buildList finalList [] = do
        Set.fromList <$> Monad.mapM (createSyncedBranch info finalList) (List.subsequences (map snd finalList))
    buildList listSoFar (td:remaining) = do
        Set.unions <$> Monad.mapM (\bd -> buildList (listSoFar ++ [(bd, td)]) remaining) (Set.toList (tBranchData td))
    -- buildList
-- createSyncedBranches

-- Constructs a new branch from a number of synchronizable branches.
createSyncedBranch :: Info -> [(BranchData, ThreadData)] -> [ThreadData] -> IOC.IOC TxsDefs.BExpr
createSyncedBranch _ [] _ = error "There should be at least two elements"
createSyncedBranch _ [_] _ = error "There should be at least two elements"
createSyncedBranch (createProcInst, initFlags, newVidDecls, g, synchronizingChans) dataPerBranch initializedBranches = do
    -- Create a fresh variable for shared communication variables that are related:
    let sharedVars = map (\(bd, _td) -> concatMap (bOfferVarsPerChan bd Map.!) (Set.toList synchronizingChans)) dataPerBranch
    freshVars <- createFreshVars (Set.fromList (head sharedVars))
    let orderedFreshVars = map (freshVars Map.!) (head sharedVars)
    let freshVarPerSharedVar = Map.fromList (concatMap (\vs -> zip vs orderedFreshVars) sharedVars)
    let applyFreshVars = Subst.subst (Map.map ValExpr.cstrVar freshVarPerSharedVar) Map.empty
    
    -- Combine all ActOffers into a single new one:
    let getNewActOffer = \(bd, td) -> let applyInitEqs = if List.elem td initializedBranches then id else doActOfferSubst (Map.fromList (tInitEqs td)) in
                                        replaceVarsInActOffer freshVarPerSharedVar (applyInitEqs (bActOffer bd))
    let newActOfferPerBExpr = map getNewActOffer dataPerBranch
    
    -- Replace variables in the ParamEqs:
    let getNewParamEqs = \(bd, td) -> let applyInitEqs = if List.elem td initializedBranches then id else Subst.subst (Map.fromList (tInitEqs td)) Map.empty in
                                      let vidDeclEqs = Map.map applyFreshVars (Map.map applyInitEqs (bParamEqs bd)) in
                                        Map.insert (tInitFlag td) cstrTrue vidDeclEqs
    let newParamEqsPerBExpr = map getNewParamEqs dataPerBranch
    
    -- Construct the new guard:
    let getInitFlagValue = \flag -> if List.elem flag (map tInitFlag initializedBranches)
                                    then ValExpr.cstrVar flag
                                    else ValExpr.cstrNot (ValExpr.cstrVar flag)
    let newGuard = ValExpr.cstrAnd (Set.fromList (g : map getInitFlagValue initFlags))
    
    -- Combine everything:
    let newActOffer = addActOfferConjunct (foldl mergeActOffers (head newActOfferPerBExpr) (tail newActOfferPerBExpr)) newGuard
    let newParamEqsWithoutInitFlags = Map.union (Map.unions newParamEqsPerBExpr) (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlags ++ newVidDecls)))
    let newInitFlagValues = Map.fromSet (\_ -> cstrTrue) (Set.fromList (map (tInitFlag . snd) dataPerBranch))
    let newParamEqs = Map.union newInitFlagValues newParamEqsWithoutInitFlags
    let newProcInst = createProcInst (map (newParamEqs Map.!) (initFlags ++ newVidDecls))
    
    let newActionPref = actionPref newActOffer newProcInst
    let hiddenChansPerBExpr = map (\(bd, _td) -> bHidChans bd) dataPerBranch
    return (applyHide (Set.unions hiddenChansPerBExpr) newActionPref)
-- createSyncedBranch

leaveBranchesUnsynchronized :: Info -> [ThreadData] -> IOC.IOC (Set.Set TxsDefs.BExpr)
leaveBranchesUnsynchronized info threadData = do
    Set.unions <$> Monad.mapM doSingle threadData
  where
    doSingle :: ThreadData -> IOC.IOC (Set.Set TxsDefs.BExpr)
    doSingle td = do
        let branchData = Set.toList (tBranchData td)
        initBs <- Set.fromList <$> Monad.mapM (\bd -> createUnsyncedBranch info (bd, td) False) branchData
        succBs <- Set.fromList <$> Monad.mapM (\bd -> createUnsyncedBranch info (bd, td) True) branchData
        return (Set.union initBs succBs)
    -- doSingle
-- leaveBranchesUnsynchronized

createUnsyncedBranch :: Info -> (BranchData, ThreadData) -> Bool -> IOC.IOC TxsDefs.BExpr
createUnsyncedBranch (createProcInst, initFlags, newVidDecls, g, _synchronizingChans) (bd, td) isInitialized = do
    let newGuard = ValExpr.cstrAnd (Set.fromList [cstrBoolEq isInitialized (ValExpr.cstrVar (tInitFlag td)), g])
    let newActOffer = addActOfferConjunct (bActOffer bd) newGuard
    
    -- Re-use existing ParamEqs if possible (Map.union is left-biased):
    let newParamEqsWithoutInitFlags = Map.union (bParamEqs bd) (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlags ++ newVidDecls)))
    let newInitFlagValues = Map.singleton (tInitFlag td) cstrTrue
    let newParamEqs = Map.union newInitFlagValues newParamEqsWithoutInitFlags
    let newProcInst = createProcInst (map (newParamEqs Map.!) (initFlags ++ newVidDecls))
    
    let newActionPref = actionPref newActOffer newProcInst
    let applyInitEqs = if isInitialized then id else Subst.subst (Map.fromList (tInitEqs td)) Map.empty
    
    return (applyHide (bHidChans bd) (applyInitEqs newActionPref))
-- createUnsyncedBranch







