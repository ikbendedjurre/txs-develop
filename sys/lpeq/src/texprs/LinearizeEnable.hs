{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LinearizeEnable
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module LinearizeEnable (
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
import qualified VarId
import ActOfferFactory
import ValFactory
import SortFactory
import BehExprDefs

import BranchLinearityUtils
import ThreadUtils

type Info = ( [TxsDefs.VExpr] -> TxsDefs.BExpr    -- Function that should be used to recursively instantiate the parent process.
            , VarId.VarId                         -- Flag variable that indicates whether we are in the first thread or in the second thread.
            , [VarId.VarId]                       -- Extra variables that the parent process will have to add to the process declaration.
            , TxsDefs.VExpr                       -- Guard.
            )
-- Info

getInitFlagFalse :: Integer
getInitFlagFalse = 0

getInitFlagTrue :: Integer
getInitFlagTrue = 1

getInitFlagStop :: Integer
getInitFlagStop = -1

linearize :: TExprLinearizer
linearize createProcInst g (TxsDefs.view -> Enable thread chanOffers exitBExpr) = do
    threadData <- getThreadData "initFlag" getIntSort thread
    let (exitThreadData, nonExitThreadData) = partitionThreadData (Set.member chanIdExit) threadData
    let exitBranchData = Set.toList (tBranchData exitThreadData)
    let nonExitBranchData = Set.toList (tBranchData nonExitThreadData)
    
    let initFlag = tInitVar threadData
    let newVidDecls = map fst (tInitEqs threadData)
    let info = (createProcInst, initFlag, newVidDecls, g)
    
    unsyncedUninitedBeforeExitBranches <- Monad.mapM (createBeforeExitBranch info getInitFlagFalse threadData) nonExitBranchData
    unsyncedInitedBeforeExitBranches <- Monad.mapM (createBeforeExitBranch info getInitFlagTrue threadData) nonExitBranchData
    syncedUninitedExitBranches <- Monad.mapM (createSyncedExitBranch info chanOffers getInitFlagFalse threadData exitBExpr) exitBranchData
    syncedInitedExitBranches <- Monad.mapM (createSyncedExitBranch info chanOffers getInitFlagTrue threadData exitBExpr) exitBranchData
    
    return (TExprLinResult { lrBranches = Set.fromList (concat [ unsyncedUninitedBeforeExitBranches
                                                               , unsyncedInitedBeforeExitBranches
                                                               , syncedUninitedExitBranches
                                                               , syncedInitedExitBranches
                                                               ])
                           , lrParams = initFlag : newVidDecls
                           , lrPredefInits = Map.fromList [(initFlag, cstrInt getInitFlagFalse)]
                           , lrStopValues = Map.fromList [(initFlag, cstrInt getInitFlagStop)]
                           })
linearize _ _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

createBeforeExitBranch :: Info -> Integer -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createBeforeExitBranch info@(_createProcInst, initFlag, _newVidDecls, g) initFlagValue td bd = do
    let newEq = cstrIntEq initFlagValue (ValExpr.cstrVar initFlag)
    let newGuard = ValExpr.cstrAnd (Set.fromList [newEq, g])
    let newActOffer = addActOfferConjunct (bActOffer bd) newGuard
    let newProcInst = createNewProcInst info Map.empty getInitFlagTrue bd
    let newActionPref = actionPref newActOffer newProcInst
    
    let applyInitEqs = if initFlagValue == getInitFlagTrue then id else Subst.subst (Map.fromList (tInitEqs td)) Map.empty
    return (applyHide (bHidChans bd) (applyInitEqs newActionPref))
-- createBeforeExitBranch

createSyncedExitBranch :: Info -> [ChanOffer] -> Integer -> ThreadData -> TxsDefs.BExpr -> BranchData -> IOC.IOC TxsDefs.BExpr
createSyncedExitBranch info@(_createProcInst, initFlag, _newVidDecls, g) chanOffers initFlagValue td exitBExpr bd = do
    let newEq = cstrIntEq initFlagValue (ValExpr.cstrVar initFlag)
    let newGuard = ValExpr.cstrAnd (Set.fromList [newEq, g])
    let newActOffer = removeChanFromActOffer (addActOfferConjunct (bActOffer bd) newGuard) chanIdExit
    
    exitParamEqs <- extractParamEqs exitBExpr
    let newProcInst = createNewProcInst info exitParamEqs getInitFlagFalse bd
    let newActionPref = actionPref newActOffer newProcInst
    
    let exitSubst = Map.fromList (zip (map getChanOfferVar chanOffers) (map ValExpr.cstrVar (getOfferVarsPerChan (bActOffer bd) Map.! chanIdExit)))
    let applyExitSubst = Subst.subst exitSubst Map.empty
    
    let applyInitEqs = if initFlagValue == getInitFlagTrue then id else Subst.subst (Map.fromList (tInitEqs td)) Map.empty
    return (applyHide (bHidChans bd) (applyExitSubst (applyInitEqs newActionPref)))
-- createSyncedExitBranch

-- Because LINT wants to reduce duplication so badly...:
createNewProcInst :: Info -> Map.Map VarId.VarId TxsDefs.VExpr -> Integer -> BranchData -> TxsDefs.BExpr
createNewProcInst (createProcInst, initFlag, newVidDecls, _g) assignedParams nextInitFlagValue bd =
    let newParamEqsWithoutInitFlags = Map.union (bParamEqs bd) (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlag : newVidDecls))) in
    let newInitFlagValues = Map.singleton initFlag (cstrInt nextInitFlagValue) in
    let newParamEqs = Map.union newInitFlagValues (Map.union assignedParams newParamEqsWithoutInitFlags) in
      createProcInst (map (newParamEqs Map.!) (initFlag : newVidDecls))
-- createNewProcInst

















