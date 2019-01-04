{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEParElm
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEParElm (
parElm
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import qualified EnvCore as IOC
import qualified EnvData
import qualified FreeVar
import qualified VarId
import LPEOps
import LPEParRemoval

-- Eliminates inert parameters (=parameters that do not contribute to the behavior of a process) from an LPE:
parElm :: LPEOperation
parElm lpe _out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<parElm>>" ]
    let allParams = Set.fromList (Map.keys (lpeInitEqs lpe))
    let guardParams = Set.unions (map (Set.fromList . FreeVar.freeVars . getGuard) (Set.toList (lpeSummands lpe)))
    -- All parameters are initially assumed to be inert, except those used in a guard.
    -- This initial set of inert parameters is reduced until a fixpoint is reached:
    let inertParams = getInertParams lpe (allParams Set.\\ guardParams)
    -- The remaining inert parameters are removed from the LPE:
    newLpe <- removeParsFromLPE inertParams lpe
    return (Right newLpe)
  where
    getGuard :: LPESummand -> TxsDefs.VExpr
    getGuard (LPESummand _ _ guard _) = guard
-- parElm

-- Loops until no more parameters are removed to the set of (presumably) inert parameters:
getInertParams :: LPE -> Set.Set VarId.VarId -> Set.Set VarId.VarId
getInertParams lpe inertParams =
    let newInertParams = removeVarsAssignedToNonInertParams (Set.toList (lpeSummands lpe)) inertParams in
      if newInertParams /= inertParams
      then getInertParams lpe newInertParams
      else newInertParams
-- getInertParams

-- Removes from the set of inert parameter all variables (=superset of parameters) that are assigned to parameters that are NOT inert:
removeVarsAssignedToNonInertParams :: [LPESummand] -> Set.Set VarId.VarId -> Set.Set VarId.VarId
removeVarsAssignedToNonInertParams summands inertParams =
    inertParams Set.\\ Set.unions (map getParamsAssignedToNonInertParams summands)
  where
    getParamsAssignedToNonInertParams :: LPESummand -> Set.Set VarId.VarId
    getParamsAssignedToNonInertParams summand =
        Set.unions (map (\(p, v) -> if Set.member p inertParams then Set.empty else Set.fromList (FreeVar.freeVars v)) (Map.toList (lpeSmdEqs summand)))
-- parElmForAllSummands

