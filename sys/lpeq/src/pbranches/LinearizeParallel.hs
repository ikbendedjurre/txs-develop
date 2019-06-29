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
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
-- import qualified EnvData
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
import SetUnions

type Info = ( [TxsDefs.VExpr] -> TxsDefs.BExpr    -- Function that should be used to recursively instantiate the parent process.
            , [VarId.VarId]                       -- Extra variables that the parent process will have to add to the process declaration.
                                                  -- First of these variables is a flag to indicate that the extra variables have been initialized.
            , TxsDefs.VExpr                       -- Guard.
            )
-- Info

linearize :: PBranchLinearizer
linearize createProcInst g (TxsDefs.view -> Parallel synchronizedChans bexprs) = do
    -- We require that all occurring variables are unique!
    Monad.mapM_ ensureFreshVarsInProcInst bexprs
    
    -- IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("synchronizedChans = " ++ show synchronizedChans) ]
    -- IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("length bexprs = " ++ show (length bexprs)) ]
    -- IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("bexprs = " ++ TxsShow.fshow bexprs) ]
    
    -- Extract data from all parallel sub-expressions:
    dataPerBExpr <- Monad.mapM extractProcInstData bexprs
    
    -- List all channel combinations used in the branches;
    -- then partition them into channel combinations that must synchronize and channel combinations that must not.
    let allCidSets = Set.unions (map (Set.map getBranchChans . fst) dataPerBExpr)
    let (syncedCidSets, unsyncedCidSets) = Set.partition (\c -> Set.intersection c synchronizedChans /= Set.empty) allCidSets
    
    let syncedDataPerBExpr = map (\(bs, eqs) -> (Set.filter (\b -> Set.member (getBranchChans b) syncedCidSets) bs, eqs)) dataPerBExpr
    let unsyncedDataPerBExpr = map (\(bs, eqs) -> (Set.filter (\b -> Set.member (getBranchChans b) unsyncedCidSets) bs, eqs)) dataPerBExpr
    
    -- Set variable declarations required by the new branches:
    initFlag <- createFreshBoolVarFromPrefix "initFlag"
    let newVidDecls = initFlag:concatMap (map fst . snd) dataPerBExpr
    
    -- ...
    let info = (createProcInst, newVidDecls, g)
    syncedBranches <- createSyncedBranches synchronizedChans info syncedDataPerBExpr
    unsyncedBranches <- createUnsyncedBranches synchronizedChans info unsyncedDataPerBExpr
    
    return (Set.union syncedBranches unsyncedBranches, newVidDecls)
linearize _ _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

data BExprData = BExprData { bHiddenChans :: Set.Set ChanId.ChanId
                           , bActOffer :: ActOffer
                           , bParamEqs :: Map.Map VarId.VarId TxsDefs.VExpr
                           , bVars :: Set.Set VarId.VarId
                           , bVizVars :: Set.Set VarId.VarId
                           , bHidVars :: Set.Set VarId.VarId
                           , bChans :: Set.Set ChanId.ChanId
                           , bOfferVarsPerChan :: Map.Map ChanId.ChanId [VarId.VarId]
                           , bSyncedChans :: Set.Set ChanId.ChanId
                           }
-- BExprData

extractBExprData :: Set.Set ChanId.ChanId -> TxsDefs.BExpr -> IOC.IOC BExprData
extractBExprData synchronizedChans bexpr = do
    let (hiddenChans, actOffer, recProcInst) = getBranchSegments bexpr
    (_, paramEqs) <- extractProcInstData recProcInst
    let (vizVars, hidVars) = getActOfferVars actOffer
    let offerVarsPerChan = getOfferVarsPerChan actOffer
    let chans = Map.keysSet offerVarsPerChan
    return (BExprData { bHiddenChans = hiddenChans
                      , bActOffer = actOffer
                      , bParamEqs = Map.fromList paramEqs
                      , bVars = Set.union vizVars hidVars
                      , bVizVars = vizVars
                      , bHidVars = hidVars
                      , bChans = chans
                      , bOfferVarsPerChan = offerVarsPerChan
                      , bSyncedChans = Set.intersection chans synchronizedChans
                      })
-- extractBExprData

createSyncedBranches :: Set.Set ChanId.ChanId -> Info -> [ProcInstData] -> IOC.IOC (Set.Set TxsDefs.BExpr)
createSyncedBranches synchronizedChans info procInstData = do
    Set.unions <$> Monad.mapM (doSubsequence []) (List.subsequences procInstData)
  where
    doSubsequence :: [(BExprData, [(VarId.VarId, TxsDefs.VExpr)])] -> [ProcInstData] -> IOC.IOC (Set.Set TxsDefs.BExpr)
    doSubsequence soFar [] = do
        initBs <- Set.fromList <$> synchronizeInit info soFar
        succBs <- Set.fromList <$> synchronizeSucc info soFar
        return (Set.union initBs succBs)
    doSubsequence soFar (r:remaining) = do
        newBExprData <- Monad.mapM (extractBExprData synchronizedChans) (Set.toList (fst r))
        Set.unions <$> Monad.mapM (\d -> doSubsequence (soFar ++ [(d, snd r)]) remaining) newBExprData
    -- doSubsequence
-- createSyncedBranches

-- Constructs a new branch from a number of synchronizable branches.
synchronizeInit :: Info -> [(BExprData, [(VarId.VarId, TxsDefs.VExpr)])] -> IOC.IOC [TxsDefs.BExpr]
synchronizeInit (_, [], _) _ = error "Unexpected input, missing initialization flag!"
synchronizeInit _ [] = return []
synchronizeInit _ [_] = return []
synchronizeInit (createProcInst, initFlag:newVidDecls, g) dataPerBExpr = do
    let sharedChans = setIntersections (map (bChans . fst) dataPerBExpr)
    if List.all (sharedChans ==) (map (bSyncedChans . fst) dataPerBExpr)
    then do -- Create a fresh variable for shared communication variables that are related:
            let sharedVars = map (\d -> concatMap (bOfferVarsPerChan (fst d) Map.!) sharedChans) dataPerBExpr
            freshVarPerSharedVar <- createFreshVars (Set.fromList (head sharedVars))
            let orderedFreshVars = map (freshVarPerSharedVar Map.!) (head sharedVars)
            let freshVarSubst = Map.fromList (concatMap (\vs -> zip vs orderedFreshVars) sharedVars)
            
            -- Expand the substitution so that it contains conversions for all variables:
            let allVars = concatMap (Set.toList . bVars . fst) dataPerBExpr
            let allVarSubst = Map.union freshVarSubst (Map.fromList (zip allVars allVars))
            let allVarValSubst = Map.map ValExpr.cstrVar allVarSubst
            
            -- Replace variables in the ActOffers:
            let newActOfferPerBExpr = map (replaceVarsInActOffer allVarSubst . bActOffer . fst) dataPerBExpr
            
            -- Combine all ActOffers into a single new one:
            let g' = ValExpr.cstrAnd (Set.fromList [ValExpr.cstrNot (ValExpr.cstrVar initFlag), g])
            let newActOffer = addActOfferConjunct (foldl mergeActOffers (head newActOfferPerBExpr) (tail newActOfferPerBExpr)) g'
            
            -- Replace variables in the ParamEqs:
            let getNewParamEqs = \(bexprData, paramEqs) -> Map.map (Subst.subst (Map.fromList paramEqs) Map.empty . Subst.subst allVarValSubst Map.empty) (bParamEqs bexprData)
            let newParamEqsPerBExpr = map getNewParamEqs dataPerBExpr
            
            -- Merge all ParamEqs, and add all parameters that are not used by the synchronized processes:
            let newParamEqs = Map.union (Map.unions newParamEqsPerBExpr) (Map.fromSet ValExpr.cstrVar (Set.fromList newVidDecls))
            let newProcInst = createProcInst (cstrTrue:map (newParamEqs Map.!) newVidDecls)
            
            -- Combine into final result:
            let allHiddenChans = Set.unions (map (bHiddenChans . fst) dataPerBExpr)
            return [applyHide allHiddenChans (actionPref newActOffer newProcInst)]
    else return []
-- synchronizeInit

synchronizeSucc :: Info -> [(BExprData, [(VarId.VarId, TxsDefs.VExpr)])] -> IOC.IOC [TxsDefs.BExpr]
synchronizeSucc (_, [], _) _ = error "Unexpected input, missing initialization flag!"
synchronizeSucc _ [] = return []
synchronizeSucc _ [_] = return []
synchronizeSucc (createProcInst, initFlag:newVidDecls, g) dataPerBExpr = do
    let sharedChans = setIntersections (map (bChans . fst) dataPerBExpr)
    if List.all (sharedChans ==) (map (bSyncedChans . fst) dataPerBExpr)
    then do -- Create a fresh variable for shared communication variables that are related:
            let sharedVars = map (\d -> concatMap (bOfferVarsPerChan (fst d) Map.!) sharedChans) dataPerBExpr
            freshVarPerSharedVar <- createFreshVars (Set.fromList (head sharedVars))
            let orderedFreshVars = map (freshVarPerSharedVar Map.!) (head sharedVars)
            let freshVarSubst = Map.fromList (concatMap (\vs -> zip vs orderedFreshVars) sharedVars)
            
            -- Expand the substitution so that it contains conversions for all variables:
            let allVars = concatMap (Set.toList . bVars . fst) dataPerBExpr
            let allVarSubst = Map.union freshVarSubst (Map.fromList (zip allVars allVars))
            let allVarValSubst = Map.map ValExpr.cstrVar allVarSubst
            
            -- Replace variables in the ActOffers:
            let newActOfferPerBExpr = map (replaceVarsInActOffer allVarSubst . bActOffer . fst) dataPerBExpr
            
            -- Combine all ActOffers into a single new one:
            let g' = ValExpr.cstrAnd (Set.fromList [ValExpr.cstrVar initFlag, g])
            let newActOffer = addActOfferConjunct (foldl mergeActOffers (head newActOfferPerBExpr) (tail newActOfferPerBExpr)) g'
            
            -- Replace variables in the ParamEqs:
            let getNewParamEqs = \(bexprData, _paramEqs) -> Map.map (Subst.subst allVarValSubst Map.empty) (bParamEqs bexprData)
            let newParamEqsPerBExpr = map getNewParamEqs dataPerBExpr
            
            -- Merge all ParamEqs, and add all parameters that are not used by the synchronized processes:
            let newParamEqs = Map.union (Map.unions newParamEqsPerBExpr) (Map.fromSet ValExpr.cstrVar (Set.fromList newVidDecls))
            let newProcInst = createProcInst (cstrTrue:map (newParamEqs Map.!) newVidDecls)
            
            -- Combine into final result:
            let allHiddenChans = Set.unions (map (bHiddenChans . fst) dataPerBExpr)
            return [applyHide allHiddenChans (actionPref newActOffer newProcInst)]
    else return []
-- synchronizeSucc

createUnsyncedBranches :: Set.Set ChanId.ChanId -> Info -> [ProcInstData] -> IOC.IOC (Set.Set TxsDefs.BExpr)
createUnsyncedBranches synchronizedChans info procInstData = do
    Set.unions <$> Monad.mapM doSingle procInstData
  where
    doSingle :: ProcInstData -> IOC.IOC (Set.Set TxsDefs.BExpr)
    doSingle r = do
        bexprDataList <- Monad.mapM (extractBExprData synchronizedChans) (Set.toList (fst r))
        initBs <- Set.fromList <$> concat <$> Monad.mapM (\d -> unsynchronizeInit info (d, snd r)) bexprDataList
        succBs <- Set.fromList <$> concat <$> Monad.mapM (\d -> unsynchronizeSucc info (d, snd r)) bexprDataList
        return (Set.union initBs succBs)
    -- doSingle
-- createUnsyncedBranches

unsynchronizeInit :: Info -> (BExprData, [(VarId.VarId, TxsDefs.VExpr)]) -> IOC.IOC [TxsDefs.BExpr]
unsynchronizeInit (_, [], _) _ = error "Unexpected input, missing initialization flag!"
unsynchronizeInit (createProcInst, initFlag:newVidDecls, g) (bexprData, paramEqs) = do
    let g' = ValExpr.cstrAnd (Set.fromList [ValExpr.cstrNot (ValExpr.cstrVar initFlag), g])
    let newActOffer = addActOfferConjunct (bActOffer bexprData) g'
    let newParamEqs = Map.map (Subst.subst (Map.fromList paramEqs) Map.empty) (bParamEqs bexprData)
    let newParamEqs' = Map.union newParamEqs (Map.fromSet ValExpr.cstrVar (Set.fromList newVidDecls))
    let newProcInst = createProcInst (cstrTrue:map (newParamEqs' Map.!) newVidDecls)
    return [applyHide (bHiddenChans bexprData) (actionPref newActOffer newProcInst)]
-- unsynchronizeInit

unsynchronizeSucc :: Info -> (BExprData, [(VarId.VarId, TxsDefs.VExpr)]) -> IOC.IOC [TxsDefs.BExpr]
unsynchronizeSucc (_, [], _) _ = error "Unexpected input, missing initialization flag!"
unsynchronizeSucc (createProcInst, initFlag:newVidDecls, g) (bexprData, _paramEqs) = do
    let g' = ValExpr.cstrAnd (Set.fromList [ValExpr.cstrVar initFlag, g])
    let newActOffer = addActOfferConjunct (bActOffer bexprData) g'
    let newParamEqs = bParamEqs bexprData
    let newParamEqs' = Map.union newParamEqs (Map.fromSet ValExpr.cstrVar (Set.fromList newVidDecls))
    let newProcInst = createProcInst (cstrTrue:map (newParamEqs' Map.!) newVidDecls)
    return [applyHide (bHiddenChans bexprData) (actionPref newActOffer newProcInst)]
-- unsynchronizeSucc







