{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LinearizeInterrupt
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module LinearizeInterrupt (
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
import VarFactory
import SortFactory
import BehExprDefs

import BranchLinearityUtils
import ThreadUtils
import UniqueObjects

type Info = ( [TxsDefs.VExpr] -> TxsDefs.BExpr    -- Function that should be used to recursively instantiate the parent process.
            , VarId.VarId                         -- Flag variable that indicates whether the thread (LHS) has been initialized.
            , VarId.VarId                         -- Flag variable that indicates whether the exit expression (RHS) has been initialized.
                                                  -- This means that the thread cannot (or can no longer) cause new behaviour!
            , [VarId.VarId]                       -- Extra variables that the parent process will have to add to the process declaration.
            , TxsDefs.VExpr                       -- Guard.
            )
-- Info

getExitFlagIdle :: Integer
getExitFlagIdle = 0

getExitFlagInited :: Integer
getExitFlagInited = 1

getExitFlagCancelled :: Integer
getExitFlagCancelled = 2

linearize :: TExprLinearizer
linearize createProcInst g (TxsDefs.view -> Interrupt thread1 thread2) = do
    -- We require that the two thread processes are unique, as well as all variables that they declare!
    [thread1', thread2'] <- ensureDistinguishableThreads [thread1, thread2]
    Monad.mapM_ ensureFreshVarsInProcInst [thread1', thread2']
    
    threadData1 <- getThreadData "initFlag" getBoolSort thread1'
    let (exitThreadData1, nonExitThreadData1) = partitionThreadData (Set.member chanIdExit) threadData1
    let exitBranchData = Set.toList (tBranchData exitThreadData1)
    let nonExitBranchData = Set.toList (tBranchData nonExitThreadData1)
    
    threadData2 <- getThreadData "initFlag" getIntSort thread2'
    let (exitThreadData2, nonExitThreadData2) = partitionThreadData (Set.member chanIdExit) threadData2
    let exitBranchData = Set.toList (tBranchData exitThreadData2)
    let nonExitBranchData = Set.toList (tBranchData nonExitThreadData2)
    
    let initFlag1 = tInitVar threadData1
    let initFlag2 = tInitVar threadData2
    let newVidDecls = map fst (tInitEqs threadData1) ++ map fst (tInitEqs threadData2)
    let info = (createProcInst, initFlag1, initFlag2, newVidDecls, g)
    
    -- Uninitialized thread can take actions while the right-hand expression is idle (and not cancelled, which implies that the thread is already initialized).
    -- Initialized thread can take actions while the right-hand expression is idle or cancelled.
    lhsUninitedNonExitBranches <- Monad.mapM (createLhsNonExitBranch info False getExitFlagIdle threadData) nonExitBranchData
    lhsInitedNonExitBranches1 <- Monad.mapM (createLhsNonExitBranch info True getExitFlagIdle threadData) nonExitBranchData
    lhsInitedNonExitBranches2 <- Monad.mapM (createLhsNonExitBranch info True getExitFlagCancelled threadData) nonExitBranchData
    
    -- Thread can cancel the right-hand expression if it is idle:
    lhsUninitedExitBranches <- Monad.mapM (createLhsExitBranch info False getExitFlagIdle threadData) exitBranchData
    lhsInitedExitBranches <- Monad.mapM (createLhsExitBranch info True getExitFlagIdle threadData) exitBranchData
    
    -- Thread can do EXIT if the right-hand expression has already been cancelled (which implies that the thread is already initialized):
    lhsInitedSemiExitBranches <- Monad.mapM (createLhsNonExitBranch info True getExitFlagCancelled threadData) nonExitBranchData
    
    -- Right-hand expression can kill the thread.
    -- (The result has no action prefix, so we rely on TExprLinearization to do another round of prefix resolution.)
    rhsBranch <- createRhsBranch info exitBExpr
    
    return (TExprLinResult { lrBranches = Set.fromList (concat [ lhsUninitedNonExitBranches
                                                               , lhsInitedNonExitBranches1
                                                               , lhsInitedNonExitBranches2
                                                               , lhsUninitedExitBranches
                                                               , lhsInitedExitBranches
                                                               , lhsInitedSemiExitBranches
                                                               , [rhsBranch]
                                                               ])
                           , lrParams = initFlag1 : initFlag2 : newVidDecls
                           , lrPredefInits = Map.fromList [(initFlag1, cstrFalse), (initFlag2, cstrInt getExitFlagIdle)]
                           })
linearize _ _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

createLhsNonExitBranch :: Info -> Bool -> Integer -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createLhsNonExitBranch info@(_createProcInst, initFlag1, initFlag2, _newVidDecls, g) initFlagValue1 initFlagValue2 td bd = do
    let newGuard = ValExpr.cstrAnd (Set.fromList [cstrBoolEq initFlagValue1 (ValExpr.cstrVar initFlag1), cstrIntEq initFlagValue2 (ValExpr.cstrVar initFlag2), g])
    let newActOffer = addActOfferConjunct (bActOffer bd) newGuard
    let newProcInst = createNewProcInst info True initFlagValue2 bd
    let newActionPref = actionPref newActOffer newProcInst
    
    let applyInitEqs = if initFlagValue1 then id else Subst.subst (Map.fromList (tInitEqs td)) Map.empty
    return (applyHide (bHidChans bd) (applyInitEqs newActionPref))
-- createLhsNonExitBranch

createLhsExitBranch :: Info -> Bool -> Integer -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createLhsExitBranch info@(_createProcInst, initFlag1, initFlag2, _newVidDecls, g) initFlagValue1 initFlagValue2 td bd = do
    let newGuard = ValExpr.cstrAnd (Set.fromList [cstrBoolEq initFlagValue1 (ValExpr.cstrVar initFlag1), cstrIntEq initFlagValue2 (ValExpr.cstrVar initFlag2), g])
    let newActOffer = removeChanFromActOffer (addActOfferConjunct (bActOffer bd) newGuard) chanIdExit
    let newProcInst = createNewProcInst info True getExitFlagCancelled bd
    let newActionPref = actionPref newActOffer newProcInst
    
    let applyInitEqs = if initFlagValue1 then id else Subst.subst (Map.fromList (tInitEqs td)) Map.empty
    return (applyHide (bHidChans bd) (applyInitEqs newActionPref))
-- createNonExitBranch

createRhsBranch :: Info -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
createRhsBranch (createProcInst, initFlag1, initFlag2, newVidDecls, g) exitBExpr = do
    let newGuard = ValExpr.cstrAnd (Set.fromList [cstrIntEq getExitFlagIdle (ValExpr.cstrVar initFlag2), g])
    exitBExprParamEqs <- extractParamEqs exitBExpr
    let newParamEqsWithoutInitFlags = Map.union exitBExprParamEqs (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlag1 : initFlag2 : newVidDecls)))
    let newInitFlagValues = Map.fromList [(initFlag1, ValExpr.cstrVar initFlag1), (initFlag2, cstrInt getExitFlagInited)]
    let newParamEqs = Map.union newInitFlagValues newParamEqsWithoutInitFlags
    let newProcInst = createProcInst (map (newParamEqs Map.!) (initFlag1 : initFlag2 : newVidDecls))
    return (guard newGuard newProcInst)
-- createRhsBranch

-- Because LINT wants to reduce duplication so badly...:
createNewProcInst :: Info -> Bool -> Integer -> BranchData -> TxsDefs.BExpr
createNewProcInst (createProcInst, initFlag1, initFlag2, newVidDecls, _g) nextInitFlagValue1 nextInitFlagValue2 bd =
    let newParamEqsWithoutInitFlags = Map.union (bParamEqs bd) (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlag1 : initFlag2 : newVidDecls))) in
    let newInitFlagValues = Map.fromList [(initFlag1, cstrBool nextInitFlagValue1), (initFlag2, cstrInt nextInitFlagValue2)] in
    let newParamEqs = Map.union newInitFlagValues newParamEqsWithoutInitFlags in
      createProcInst (map (newParamEqs Map.!) (initFlag1 : initFlag2 : newVidDecls))
-- createNewProcInst

















