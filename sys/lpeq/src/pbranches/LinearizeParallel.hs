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

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified Subst
import qualified ChanId
import qualified VarId
import ActOfferFactory
import VarFactory
import BehExprDefs

import BranchUtils
import PBranchUtils

type Info = ( [TxsDefs.VExpr] -> TxsDefs.BExpr    -- Function that should be used to recursively instantiate the parent process.
            , [VarId.VarId]                       -- Extra variables that the parent process will have to declare (in order).
            , TxsDefs.VExpr                       -- Guard.
            , Set.Set ChanId.ChanId               -- Channels that are synchronized.
            )
-- Info

linearize :: PBranchLinearizer
linearize createProcInst g (TxsDefs.view -> Parallel synchronizedChans bexprs) = do
    -- We require that all occurring variables are unique!
    Monad.mapM_ ensureFreshVarsInProcInst bexprs
    
    rs <- Monad.mapM extractProcInstBranches bexprs
    let newVidDecls = concatMap fst rs
    let branchesPerBExpr = map snd rs
    
    -- List all channel combinations used in the branches;
    -- then partition them into channel combinations that must synchronize and channel combinations that must not.
    -- (TODO Figure out the precise constraints for this!)
    let allCidSets = Set.unions (map (Set.map getBranchChans) branchesPerBExpr)
    let (syncedCidSets, unsyncedCidSets) = Set.partition (\c -> Set.intersection c synchronizedChans /= Set.empty) allCidSets
    
    let syncedBranchesPerBExpr = map (Set.filter (\b -> Set.member (getBranchChans b) syncedCidSets)) branchesPerBExpr
    let unsyncedBranchesPerBExpr = map (Set.filter (\b -> Set.member (getBranchChans b) unsyncedCidSets)) branchesPerBExpr
    
    let info = (createProcInst, newVidDecls, g, synchronizedChans)
    syncedBranches <- synchronizeBExprCombinations info syncedBranchesPerBExpr
    let unsyncedBranches = Set.unions unsyncedBranchesPerBExpr
    return (parallel synchronizedChans bexprs, Set.union syncedBranches unsyncedBranches, newVidDecls)
linearize _ _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

synchronizeBExprCombinations :: Info -> [Set.Set TxsDefs.BExpr] -> IOC.IOC (Set.Set TxsDefs.BExpr)
synchronizeBExprCombinations _ [] = return Set.empty
synchronizeBExprCombinations info (x:xs) = do
    syncedBExprs <- synchronizeBExprs info x (Set.unions xs)
    rest <- synchronizeBExprCombinations info xs
    return (Set.union syncedBExprs rest)
-- synchronizeBExprCombinations

synchronizeBExprs :: Info -> Set.Set TxsDefs.BExpr -> Set.Set TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr)
synchronizeBExprs info xs ys = do
    let combinations = [ (x, y) | x <- Set.toList xs, y <- Set.toList ys ]
    Set.fromList <$> Monad.mapM (synchronizeBranches info) combinations
-- synchronizeBExprs

synchronizeBranches :: Info -> (TxsDefs.BExpr, TxsDefs.BExpr) -> IOC.IOC TxsDefs.BExpr
synchronizeBranches (createProcInst, newVidDecls, g, synchronizedChans) (bexpr1, bexpr2) = do
    let (hiddenChans1, actOffer1, procInst1) = getBranchSegments bexpr1
    let (hiddenChans2, actOffer2, procInst2) = getBranchSegments bexpr2
    
    let (vizVars1, hidVars1) = getActOfferVars actOffer1
    let (vizVars2, hidVars2) = getActOfferVars actOffer2
    let offerVarsPerChan1 = getOfferVarsPerChan actOffer1
    let offerVarsPerChan2 = getOfferVarsPerChan actOffer2
    let offerVarsPerSyncedChan = Map.restrictKeys (Map.intersectionWith (\vs1 vs2 -> (vs1, vs2)) offerVarsPerChan1 offerVarsPerChan2) synchronizedChans
    
    let createFreshSyncedVars (vs1, vs2) = do freshVars <- createFreshVars (Set.fromList vs1)
                                              let orderedFreshVars = map (freshVars Map.!) vs1
                                              return (Map.fromList (zip vs1 orderedFreshVars ++ zip vs2 orderedFreshVars))
    freshVarsPerSyncedVar <- Map.unions <$> Monad.mapM createFreshSyncedVars (Map.elems offerVarsPerSyncedChan)
    
    -- (We rely on the fact that Map.union is left-biased:)
    let varSubst = Map.union freshVarsPerSyncedVar (Map.fromSet id (Set.unions [vizVars1, hidVars1, vizVars2, hidVars2]))
    let actOffer1' = replaceVarsInActOffer varSubst actOffer1
    let actOffer2' = replaceVarsInActOffer varSubst actOffer2
    
    let valSubst = Map.map ValExpr.cstrVar varSubst
    let procInst1' = Subst.subst valSubst Map.empty procInst1
    let procInst2' = Subst.subst valSubst Map.empty procInst2
    
    let vidIdMap = Map.fromSet ValExpr.cstrVar (Set.fromList newVidDecls)
    paramEqs1 <- extractProcInstParamEqs procInst1'
    paramEqs2 <- extractProcInstParamEqs procInst2'
    
    -- (We rely on the fact that Map.union is left-biased:)
    let vidMap = Map.union (Map.union paramEqs1 paramEqs2) vidIdMap
    
    let newActOffer = addActOfferConjunct (mergeActOffers actOffer1' actOffer2') g
    let newProcInst = createProcInst (map (vidMap Map.!) newVidDecls)
    let bexpr = actionPref newActOffer newProcInst
    return (applyHide (Set.union hiddenChans1 hiddenChans2) bexpr)
-- synchronizeBranches










