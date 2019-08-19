{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LinearizeDisable
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module LinearizeDisable (
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

type Info = ( [TxsDefs.VExpr] -> TxsDefs.BExpr    -- Function that should be used to recursively instantiate the parent process.
            , VarId.VarId                         -- Flag variable that indicates whether the thread (LHS) has been initialized.
            , VarId.VarId                         -- Flag variable that indicates whether the exit expression (RHS) has been initialized.
                                                  -- This means that the thread cannot (or can no longer) cause new behaviour!
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

getExitFlagIdle :: Integer
getExitFlagIdle = 0

getExitFlagInited :: Integer
getExitFlagInited = 1

getExitFlagCancelled :: Integer
getExitFlagCancelled = 2

getExitFlagStop :: Integer
getExitFlagStop = -1

linearize :: TExprLinearizer
linearize createProcInst g (TxsDefs.view -> Disable thread exitBExpr) = do
    threadData <- getThreadData "initFlag" getIntSort thread
    let (exitThreadData, nonExitThreadData) = partitionThreadData (Set.member chanIdExit) threadData
    let exitBranchData = Set.toList (tBranchData exitThreadData)
    let nonExitBranchData = Set.toList (tBranchData nonExitThreadData)
    
    let initFlag = tInitVar threadData
    exitFlag <- createFreshVarFromPrefix "exitFlag" getIntSort
    let newVidDecls = map fst (tInitEqs threadData)
    let info = (createProcInst, initFlag, exitFlag, newVidDecls, g)
    
    -- Uninitialized thread can take actions while the right-hand expression is idle (and not cancelled, which implies that the thread is already initialized).
    -- Initialized thread can take actions while the right-hand expression is idle or cancelled.
    lhsUninitedNonExitBranches <- Monad.mapM (createLhsNonExitBranch info getInitFlagFalse getExitFlagIdle threadData) nonExitBranchData
    lhsInitedNonExitBranches1 <- Monad.mapM (createLhsNonExitBranch info getInitFlagTrue getExitFlagIdle threadData) nonExitBranchData
    lhsInitedNonExitBranches2 <- Monad.mapM (createLhsNonExitBranch info getInitFlagTrue getExitFlagCancelled threadData) nonExitBranchData
    
    -- Thread can cancel the right-hand expression if it is idle:
    lhsUninitedExitBranches <- Monad.mapM (createLhsExitBranch info getInitFlagFalse getExitFlagIdle threadData) exitBranchData
    lhsInitedExitBranches <- Monad.mapM (createLhsExitBranch info getInitFlagTrue getExitFlagIdle threadData) exitBranchData
    
    -- Thread can do EXIT if the right-hand expression has already been cancelled (which implies that the thread is already initialized):
    lhsInitedSemiExitBranches <- Monad.mapM (createLhsNonExitBranch info getInitFlagTrue getExitFlagCancelled threadData) nonExitBranchData
    
    -- Right-hand expression can kill the thread (as long as it is not cancelled).
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
                           , lrParams = initFlag : exitFlag : newVidDecls
                           , lrPredefInits = Map.fromList [(initFlag, cstrInt getInitFlagFalse), (exitFlag, cstrInt getExitFlagIdle)]
                           , lrStopValues = Map.fromList [(initFlag, cstrInt getInitFlagStop), (exitFlag, cstrInt getExitFlagStop)]
                           })
linearize _ _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

createLhsNonExitBranch :: Info -> Integer -> Integer -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createLhsNonExitBranch info@(_createProcInst, initFlag, exitFlag, _newVidDecls, g) initFlagValue exitFlagValue td bd = do
    let newEq1 = cstrIntEq initFlagValue (ValExpr.cstrVar initFlag)
    let newEq2 = cstrIntEq exitFlagValue (ValExpr.cstrVar exitFlag)
    let newGuard = ValExpr.cstrAnd (Set.fromList [newEq1, newEq2, g])
    let newActOffer = addActOfferConjunct (bActOffer bd) newGuard
    let newProcInst = createNewProcInst info getInitFlagTrue exitFlagValue bd
    createBranch newActOffer newProcInst initFlagValue td bd
-- createLhsNonExitBranch

createLhsExitBranch :: Info -> Integer -> Integer -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createLhsExitBranch info@(_createProcInst, initFlag, exitFlag, _newVidDecls, g) initFlagValue exitFlagValue td bd = do
    let newEq1 = cstrIntEq initFlagValue (ValExpr.cstrVar initFlag)
    let newEq2 = cstrIntEq exitFlagValue (ValExpr.cstrVar exitFlag)
    let newGuard = ValExpr.cstrAnd (Set.fromList [newEq1, newEq2, g])
    let newActOffer = removeChanFromActOffer (addActOfferConjunct (bActOffer bd) newGuard) chanIdExit
    let newProcInst = createNewProcInst info getInitFlagTrue getExitFlagCancelled bd
    createBranch newActOffer newProcInst initFlagValue td bd
-- createNonExitBranch

createRhsBranch :: Info -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
createRhsBranch (createProcInst, initFlag, exitFlag, newVidDecls, g) exitBExpr = do
    let newEq = cstrIntEq getExitFlagIdle (ValExpr.cstrVar exitFlag)
    let newGuard = ValExpr.cstrAnd (Set.fromList [newEq, g])
    exitBExprParamEqs <- extractParamEqs exitBExpr
    let newParamEqsWithUnchangedInitFlags = Map.union exitBExprParamEqs (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlag : exitFlag : newVidDecls)))
    let newInitFlagValues = Map.fromList [(initFlag, ValExpr.cstrVar initFlag), (exitFlag, cstrInt getExitFlagInited)]
    let newParamEqs = Map.union newInitFlagValues newParamEqsWithUnchangedInitFlags
    let newProcInst = createProcInst (map (newParamEqs Map.!) (initFlag : exitFlag : newVidDecls))
    return (guard newGuard newProcInst)
-- createRhsBranch

-- Because LINT wants to reduce duplication so badly...:
createNewProcInst :: Info -> Integer -> Integer -> BranchData -> TxsDefs.BExpr
createNewProcInst (createProcInst, initFlag, exitFlag, newVidDecls, _g) nextInitFlagValue1 nextInitFlagValue2 bd =
    let newParamEqsWithUnchangedInitFlags = Map.union (bParamEqs bd) (Map.fromSet ValExpr.cstrVar (Set.fromList (initFlag : exitFlag : newVidDecls))) in
    let newInitFlagValues = Map.fromList [(initFlag, cstrInt nextInitFlagValue1), (exitFlag, cstrInt nextInitFlagValue2)] in
    let newParamEqs = Map.union newInitFlagValues newParamEqsWithUnchangedInitFlags in
      createProcInst (map (newParamEqs Map.!) (initFlag : exitFlag : newVidDecls))
-- createNewProcInst

-- Because LINT wants to reduce duplication so badly...:
createBranch :: TxsDefs.ActOffer -> TxsDefs.BExpr -> Integer -> ThreadData -> BranchData -> IOC.IOC TxsDefs.BExpr
createBranch newActOffer newProcInst initFlagValue td bd = do
    let newActionPref = actionPref newActOffer newProcInst
    let applyInitEqs = if initFlagValue == getInitFlagTrue then id else Subst.subst (Map.fromList (tInitEqs td)) Map.empty
    return (applyHide (bHidChans bd) (applyInitEqs newActionPref))
-- createBranch















