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
import BehExprDefs

import BranchLinearityUtils
-- import UniqueObjects
import ThreadUtils

-- import ProcSearch

type Info = ( [TxsDefs.VExpr] -> TxsDefs.BExpr    -- Function that should be used to recursively instantiate the parent process.
            , VarId.VarId                         -- Flag variable that indicates whether we are in the first thread or in the second thread.
            , VarId.VarId                         -- Flag variable that indicates whether we are in the first thread or in the second thread.
            , [VarId.VarId]                       -- Extra variables that the parent process will have to add to the process declaration.
            , TxsDefs.VExpr                       -- Guard.
            )
-- Info

linearize :: TExprLinearizer
linearize createProcInst g (TxsDefs.view -> Enable thread1 chanOffers thread2) = do
    -- We require that all thread processes are unique, as well as all variables that they declare!
    --[thread1', thread2'] <- ensureDistinguishableThreads [thread1, thread2]
    --ensureFreshVarsInProcInst thread1'
    --ensureFreshVarsInProcInst thread2'
    
    -- Extract data from all parallel sub-expressions:
    [threadData1, threadData2] <- Monad.mapM getThreadData [thread1, thread2]
    
    let initFlag1 = tInitFlag threadData1
    let initFlag2 = tInitFlag threadData2
    let newVidDecls = map fst (tInitEqs threadData1) ++ map fst (tInitEqs threadData2)
    let info = (createProcInst, initFlag1, initFlag2, newVidDecls, g)
    
    let (exitThreadData1, nonExitThreadData1) = partitionThreadData (Set.member chanIdExit) threadData1
    let exitBranchData1 = Set.toList (tBranchData exitThreadData1)
    let nonExitBranchData1 = Set.toList (tBranchData nonExitThreadData1)
    let branchData2 = Set.toList (tBranchData threadData2)
    
    unsyncedUninitedBranchesBeforeExit <- Monad.mapM (createUnsyncedBranch info False True False False threadData1) nonExitBranchData1
    unsyncedInitedBranchesBeforeExit <- Monad.mapM (createUnsyncedBranch info True True False False threadData1) nonExitBranchData1
    syncedUninitedExitBranches <- Monad.mapM (createSyncedExitBranch info chanOffers False True threadData1 threadData2) exitBranchData1
    syncedInitedExitBranches <- Monad.mapM (createSyncedExitBranch info chanOffers True True threadData1 threadData2) exitBranchData1
    unsyncedBranchesAfterExit <- Monad.mapM (createUnsyncedBranch info True True True True threadData2) branchData2
    
    return (Set.fromList (concat [ unsyncedUninitedBranchesBeforeExit
                                 , unsyncedInitedBranchesBeforeExit
                                 , syncedUninitedExitBranches
                                 , syncedInitedExitBranches
                                 , unsyncedBranchesAfterExit
                                 ]), initFlag1 : initFlag2 : newVidDecls)
linearize _ _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

createSyncedExitBranch :: Info -> [ChanOffer] -> Bool -> Bool -> ThreadData -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createSyncedExitBranch info@(_createProcInst, initFlag1, initFlag2, _newVidDecls, g) chanOffers initFlagValue1 nextInitFlagValue1 td1 td2 bd = do
    let newGuard = ValExpr.cstrAnd (Set.fromList [cstrBoolEq initFlagValue1 (ValExpr.cstrVar initFlag1), cstrBoolEq False (ValExpr.cstrVar initFlag2), g])
    let newActOffer = addActOfferConjunct (bActOffer bd) newGuard
    let newProcInst = createNewProcInst info nextInitFlagValue1 True bd
    let newActionPref = actionPref newActOffer newProcInst
    
    let exitParamEqs = Map.fromList (zip (map getChanOfferVar chanOffers) (map ValExpr.cstrVar (getOfferVarsPerChan (bActOffer bd) Map.! chanIdExit)))
    let applyExitParamEqs = Subst.subst (Map.union exitParamEqs (Map.fromList (tInitEqs td2))) Map.empty
    let applyInitEqs = if not initFlagValue1 then Subst.subst (Map.fromList (tInitEqs td1)) Map.empty else id
    return (applyHide (bHidChans bd) (applyExitParamEqs (applyInitEqs newActionPref)))
-- createSyncedExitBranch

createUnsyncedBranch :: Info -> Bool -> Bool -> Bool -> Bool -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createUnsyncedBranch info@(_createProcInst, initFlag1, initFlag2, _newVidDecls, g) initFlagValue1 nextInitFlagValue1 initFlagValue2 nextInitFlagValue2 td bd = do
    let newGuard = ValExpr.cstrAnd (Set.fromList [cstrBoolEq initFlagValue1 (ValExpr.cstrVar initFlag1), cstrBoolEq initFlagValue2 (ValExpr.cstrVar initFlag2), g])
    let newActOffer = addActOfferConjunct (bActOffer bd) newGuard
    let newProcInst = createNewProcInst info nextInitFlagValue1 nextInitFlagValue2 bd
    let newActionPref = actionPref newActOffer newProcInst
    
    let applyInitEqs = if ((tInitFlag td == initFlag1) && not initFlagValue1) || ((tInitFlag td == initFlag2) && not initFlagValue2) then Subst.subst (Map.fromList (tInitEqs td)) Map.empty else id
    return (applyHide (bHidChans bd) (applyInitEqs newActionPref))
-- createUnsyncedBranch

-- Because LINT wants to reduce duplication so badly...:
createNewProcInst :: Info -> Bool -> Bool -> BranchData -> TxsDefs.BExpr
createNewProcInst (createProcInst, initFlag1, initFlag2, newVidDecls, _g) nextInitFlagValue1 nextInitFlagValue2 bd =
    let newParamEqsWithoutInitFlags = Map.union (bParamEqs bd) (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlag1 : initFlag2 : newVidDecls))) in
    let newInitFlagValues = Map.fromList [(initFlag1, cstrBool nextInitFlagValue1), (initFlag2, cstrBool nextInitFlagValue2)] in
    let newParamEqs = Map.union newInitFlagValues newParamEqsWithoutInitFlags in
      createProcInst (map (newParamEqs Map.!) (initFlag1 : initFlag2 : newVidDecls))
-- createNewProcInst

















