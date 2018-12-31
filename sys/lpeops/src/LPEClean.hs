{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEClean
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEClean (
cleanLPE
) where

import qualified Data.List           as List
import qualified Data.Map            as Map
import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified EnvData
import qualified ChanId
import qualified TxsDefs
import qualified VarId
import qualified ValExpr
import LPEOps
import LPESuccessors
import Satisfiability

-- Removes duplicate summands and summands that are unreachable by all other (!) summands
-- (so basically we do a partial, symbolic reachability analysis).
cleanLPE :: LPEOperation
cleanLPE (tdefs, mdef, (n, channels, initParamEqs, summands)) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<clean>>" ]
    uniqueSummands <- Monad.foldM addSummandIfUnique Set.empty (Set.toList summands)
    Monad.when (length uniqueSummands < Set.size summands) (IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Removed " ++ show (Set.size summands - length uniqueSummands) ++ " duplicate summands") ])
    initReachableSummands <- Monad.foldM addSummandIfReachableFromInit Set.empty uniqueSummands
    reachableSummands <- reachableSummandsLoop initReachableSummands invariant (uniqueSummands Set.\\ initReachableSummands)
    Monad.when (length reachableSummands < length uniqueSummands) (IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Removed " ++ show (length uniqueSummands - length reachableSummands) ++ " unreachable summands") ])
    return (Right (tdefs, mdef, (n, channels, initParamEqs, reachableSummands)))
  where
    addSummandIfUnique :: Set.Set LPESummand -> LPESummand -> IOC.IOC (Set.Set LPESummand)
    addSummandIfUnique soFar candidate = do
        found <- containsSummand (Set.toList soFar) invariant candidate
        if found
        then return soFar
        else return (Set.insert candidate soFar)
    -- addSummandIfUnique
    
    addSummandIfReachableFromInit :: Set.Set LPESummand -> LPESummand -> IOC.IOC (Set.Set LPESummand)
    addSummandIfReachableFromInit soFar candidate@(LPESummand _channelVars _channelOffers guard _paramEqs) = do
        -- Check if the summand can be reached via the initial state:
        guard' <- doBlindSubst initParamEqs guard
        sat <- couldBeSatisfiable guard' invariant
        if sat
        then return (Set.insert candidate soFar)
        else return soFar
    -- addSummandIfReachableFromInit
-- cleanLPE

reachableSummandsLoop :: Set.Set LPESummand -> TxsDefs.VExpr -> Set.Set LPESummand -> IOC.IOC (Set.Set LPESummand)
reachableSummandsLoop reachableSummands invariant summands = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Reached " ++ show (Set.size reachableSummands) ++ " of " ++ show (Set.size reachableSummands + Set.size summands) ++ " summands") ]
    newReachableSummands <- Monad.foldM (updateReachableSummands reachableSummands invariant) reachableSummands summands
    if newReachableSummands /= reachableSummands
    then reachableSummandsLoop newReachableSummands invariant (summands Set.\\ newReachableSummands)
    else return newReachableSummands
-- reachableSummandsLoop

updateReachableSummands :: Set.Set LPESummand -> TxsDefs.VExpr -> Set.Set LPESummand -> LPESummand -> IOC.IOC (Set.Set LPESummand)
updateReachableSummands reachableSummands invariant soFar summand = do
    -- Check which summands could possibly enable this summand:
    predecessors <- getPossiblePredecessors reachableSummands invariant summand
    -- If the summand is enabled by other summands than itself, it must be reachable:
    let predecessorsSet = Set.delete summand (Set.fromList predecessors)
    if predecessorsSet /= Set.empty
    then return (Set.insert summand soFar)
    else return soFar
-- updateReachableSummands

containsSummand :: [LPESummand] -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
containsSummand [] _ _ = return False
containsSummand (x:xs) invariant summand = do
    equiv <- isEquivalentSummand x summand invariant
    if equiv
    then return True
    else containsSummand xs invariant summand
-- containsSummand

isEquivalentSummand :: LPESummand -> LPESummand -> TxsDefs.VExpr -> IOC.IOC Bool
isEquivalentSummand (LPESummand _vars1 chans1 guard1 paramEqs1) (LPESummand _vars2 chans2 guard2 paramEqs2) invariant = do
    let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
    let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
    if map fst sortedChans1 /= map fst sortedChans2
    then return False
    else do let chanVars1 = concatMap snd sortedChans1
            let chanVars2 = concatMap snd sortedChans2
            let subst = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) chanVars1 chanVars2)
            guard2' <- doBlindSubst subst guard2
            let guardEq = ValExpr.cstrEqual guard1 guard2'
            procInstEqs <- Monad.mapM (getProcInstEq subst paramEqs2) (Map.toList paramEqs1)
            isTautology (ValExpr.cstrAnd (Set.fromList (guardEq:procInstEqs))) invariant
  where
    getProcInstEq :: Map.Map VarId.VarId TxsDefs.VExpr -> LPEParamEqs -> (VarId.VarId, TxsDefs.VExpr) -> IOC.IOC TxsDefs.VExpr
    getProcInstEq subst eqs2 (p1, v1) = do
        let v2 = eqs2 Map.! p1
        v2' <- doBlindSubst subst v2
        return (ValExpr.cstrEqual v1 v2')
-- isEquivalentSummand













