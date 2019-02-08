{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPECompareSmds
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPECompareSmds (
isEquivalentSummand,
isContainedSummand,
removeContainedSummands
) where

import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Set as Set
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ValExpr
import qualified VarId
import qualified Constant
import qualified Satisfiability as Sat
import LPETypes
import BlindSubst

-- Checks if two summands are (definitely) equivalent.
-- This means that the two summands add the exact same behavior to an LPE.
-- It is an under-approximation: two summands can be equivalent even though this function returns false!
isEquivalentSummand :: LPESummand -> LPESummand -> TxsDefs.VExpr -> IOC.IOC Bool
isEquivalentSummand summand1 summand2 invariant = do
    -- Both summands must communicate over the same channel:
    if lpeSmdChan summand1 /= lpeSmdChan summand2
    then return False
    else do let useChanVars1 = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) (lpeSmdVars summand1) (lpeSmdVars summand2))
            -- Check whether both guards are definitely enabled at the same time with the following expression:
            guard2' <- doBlindSubst useChanVars1 (lpeSmdGuard summand2)
            let guardEq = ValExpr.cstrEqual (lpeSmdGuard summand1) guard2'
            -- Check whether both summands definitely lead to the same next-state with the following expressions:
            procInstEqs <- Monad.mapM (getProcInstEq useChanVars1 (lpeSmdEqs summand2)) (Map.toList (lpeSmdEqs summand1))
            -- Check:
            Sat.isTautology (ValExpr.cstrAnd (Set.fromList (guardEq:procInstEqs))) invariant
  where
    getProcInstEq :: Map.Map VarId.VarId TxsDefs.VExpr -> LPEParamEqs -> (VarId.VarId, TxsDefs.VExpr) -> IOC.IOC TxsDefs.VExpr
    getProcInstEq useChanVars1 eqs2 (p1, v1) = do
        let v2 = eqs2 Map.! p1
        v2' <- doBlindSubst useChanVars1 v2
        return (ValExpr.cstrEqual v1 v2')
-- isEquivalentSummand

-- Checks if the first summand (definitely) 'contains' the second command.
-- This means that the first summand adds behavior to an LPE that is a superset of the behavior that the second summand adds.
-- It is an under-approximation: the first summand can 'contain' the second summand even though this function returns false!
isContainedSummand :: LPESummand -> LPESummand -> TxsDefs.VExpr -> IOC.IOC Bool
isContainedSummand summand1 summand2 invariant = do
    -- Both summands must communicate over the same channel:
    if lpeSmdChan summand1 /= lpeSmdChan summand2
    then return False
    else do let useChanVars1 = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) (lpeSmdVars summand1) (lpeSmdVars summand2))
            -- Check whether both guards are definitely enabled at the same time with the following expression:
            guard2' <- doBlindSubst useChanVars1 (lpeSmdGuard summand2)
            let guardEq = ValExpr.cstrITE guard2' (lpeSmdGuard summand1) (ValExpr.cstrConst (Constant.Cbool True))
            -- Check whether both summands definitely lead to the same next-state with the following expressions:
            procInstEqs <- Monad.mapM (getProcInstEq useChanVars1 (lpeSmdEqs summand2)) (Map.toList (lpeSmdEqs summand1))
            -- Check:
            Sat.isTautology (ValExpr.cstrAnd (Set.fromList (guardEq:procInstEqs))) invariant
  where
    getProcInstEq :: Map.Map VarId.VarId TxsDefs.VExpr -> LPEParamEqs -> (VarId.VarId, TxsDefs.VExpr) -> IOC.IOC TxsDefs.VExpr
    getProcInstEq useChanVars1 eqs2 (p1, v1) = do
        let v2 = eqs2 Map.! p1
        v2' <- doBlindSubst useChanVars1 v2
        return (ValExpr.cstrEqual v1 v2')
-- isContainedSummand

-- Only leaves summands in the set that are not 'contained' by another summand in the same set.
removeContainedSummands :: Set.Set LPESummand -> TxsDefs.VExpr -> IOC.IOC (Set.Set LPESummand)
removeContainedSummands summands invariant = Set.fromList <$> Monad.filterM isNotContainedByOthers (Set.toList summands)
  where
    isNotContainedByOthers :: LPESummand -> IOC.IOC Bool
    isNotContainedByOthers summand = do
        containers <- Monad.filterM (\c -> isContainedSummand c summand invariant) (Set.toList (Set.delete summand summands))
        return (containers == [])
-- removeContainedSummands



