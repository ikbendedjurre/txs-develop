{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEConfCheck
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEConfCheck (
chanIdConfluentIstep,
confCheck,
confElm
) where

import qualified Data.Map            as Map
import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified EnvData
import qualified VarId
import qualified TxsDefs
import qualified Satisfiability as Sat
import           LPEOps
import           ValExpr
import           Constant
import           LPESuccessors
import           LPEBlindSubst

chanIdConfluentIstep :: TxsDefs.ChanId
chanIdConfluentIstep = TxsDefs.ChanId (Text.pack "CISTEP") 969 []

getConfluentTauSummands :: LPESummands -> TxsDefs.VExpr -> IOC.IOC LPESummands
getConfluentTauSummands summands invariant = do
    confluentTauSummands <- Monad.filterM (isConfluentTauSummand (Set.toList summands) invariant) (filter isTauSummand (Set.toList summands))
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Detected " ++ show (length confluentTauSummands) ++ " confluent ISTEP summand(s)!") ]
    return (Set.fromList confluentTauSummands)
-- getConfluentTauSummands

-- LPE rewrite method.
-- Flags confluent ISTEPs by renaming them to CISTEPs.
confCheck :: LPEOperation
confCheck lpe _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<confCheck>>" ]
    confluentTauSummands <- getConfluentTauSummands (lpeSummands lpe) invariant
    let noConfluentTauSummands = (lpeSummands lpe) Set.\\ confluentTauSummands
    let newSummands = Set.union noConfluentTauSummands (Set.map flagTauSummand confluentTauSummands)
    return (Right (lpe { lpeSummands = newSummands }))
-- confCheck

isTauSummand :: LPESummand -> Bool
isTauSummand (LPESummand { lpeSmdOffers = offers }) =
    case Map.toList offers of
        [(cid, _)] -> cid == TxsDefs.chanIdIstep
        _ -> False
-- isTauSummand

flagTauSummand :: LPESummand -> LPESummand
flagTauSummand summand@(LPESummand { lpeSmdOffers = offers }) =
    case Map.toList offers of
        [(_, commVars)] -> summand { lpeSmdOffers = Map.singleton chanIdConfluentIstep commVars }
        _ -> summand
-- flagTauSummand

isConfluentTauSummand :: [LPESummand] -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
isConfluentTauSummand [] _ _ = return True
isConfluentTauSummand (x:xs) invariant tauSummand = do
    check <- checkConfluenceCondition tauSummand x invariant
    if check
    then isConfluentTauSummand xs invariant tauSummand
    else return False
-- isConfluentTauSummand

checkConfluenceCondition :: LPESummand -> LPESummand -> TxsDefs.VExpr -> IOC.IOC Bool
checkConfluenceCondition summand1 summand2 invariant =
    if summand1 == summand2
    then return True
    else do -- a1 == a1[g1] && ... && an == an[g1]
            channelArgEqs <- Monad.mapM getChannelArgEq (Set.toList (lpeSmdVars summand2))
            
            -- x1[g1][g2] == x1[g2][g1] && ... && xn[g1][g2] == xn[g2][g1]
            instantiationEqs <- Monad.mapM getInstantiationEq (Map.keys (lpeSmdEqs summand2))
            
            -- c1 && c2
            let premise = cstrAnd (Set.fromList [lpeSmdGuard summand1, lpeSmdGuard summand2])
            
            -- c1[g2] && c2[g1] && ...
            g1 <- doBlindSubst (lpeSmdEqs summand2) (lpeSmdGuard summand1)
            g2 <- doBlindSubst (lpeSmdEqs summand1) (lpeSmdGuard summand2)
            let conclusion = cstrAnd (Set.fromList ([g1, g2] ++ channelArgEqs ++ instantiationEqs))
            
            -- Combine them all:
            let confluenceCondition = cstrITE premise conclusion (cstrConst (Cbool True))
            
            -- Is the confluence condition a tautology?
            Sat.isTautology confluenceCondition invariant
  where
    getChannelArgEq :: VarId.VarId -> IOC.IOC TxsDefs.VExpr
    getChannelArgEq param = do
        let paramExpr = cstrVar param
        e' <- doBlindSubst (lpeSmdEqs summand1) paramExpr
        return (cstrEqual paramExpr e')
    -- getChannelArgEq
    
    getInstantiationEq :: VarId.VarId -> IOC.IOC TxsDefs.VExpr
    getInstantiationEq param = do
        let paramExpr = cstrVar param
        e1 <- doBlindSubst (lpeSmdEqs summand2) paramExpr
        e1' <- doBlindSubst (lpeSmdEqs summand1) e1
        e2 <- doBlindSubst (lpeSmdEqs summand1) paramExpr
        e2' <- doBlindSubst (lpeSmdEqs summand2) e2
        return (cstrEqual e1' e2')
    -- getInstantiationEq
-- checkConfluenceCondition

-- LPE rewrite method.
-- Appends confluent ISTEPs to predecessor summands.
confElm :: LPEOperation
confElm lpe _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<confElm>>" ]
    confluentTauSummands <- getConfluentTauSummands (lpeSummands lpe) invariant
    if confluentTauSummands == Set.empty
    then return $ Right lpe
    else do let orderedSummands = Set.toList (lpeSummands lpe)
            definiteSuccessors <- Monad.mapM (getDefiniteSuccessors (lpeSummands lpe) invariant) orderedSummands
            let confluentTauSuccessors = map (Set.toList . Set.intersection confluentTauSummands . Set.fromList) definiteSuccessors
            mergedSummands <- Monad.mapM mergeZippedSummands (zip orderedSummands confluentTauSuccessors)
            return $ Right (lpe { lpeSummands = Set.fromList mergedSummands })
  where
    mergeZippedSummands :: (LPESummand, [LPESummand]) -> IOC.IOC LPESummand
    mergeZippedSummands (summand, []) = return summand
    mergeZippedSummands (summand1, summand2:_) = do
        newEqs <- doBlindParamEqsSubst (lpeSmdEqs summand1) (lpeSmdEqs summand2)
        return (summand1 { lpeSmdEqs = newEqs })
-- confElm

