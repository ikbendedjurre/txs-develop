{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEQExec
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module LPEQLinearization (
linearize
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ValExpr
import qualified Constant
import qualified ProcId
import qualified ProcDef
import BehExprDefs
import ProcIdFactory
import VarFactory
import SortFactory

import LPEQComp
import LPEQParallel

type UpdatedProcInst = [Either Int TxsDefs.BExpr]
type LinearizationState = (TxsDefs.BExpr, Map.Map ProcId.ProcId UpdatedProcInst)

linearize :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
linearize bexpr = do
    ([bexpr'], _) <- linearizeRecursive ([], Map.empty) bexpr
    return bexpr'
-- addProgramCounters

linearizeProc :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
linearizeProc 

getLinearizedChild :: LinearizationState -> IOC.IOC LPEQChild
getLinearizedChild (prevBExprs, replacedProcs) currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          do r <- getProcById pid
             case r of
               Just (ProcDef.ProcDef cidDecls (pc:vidDecls) body) ->
                   do return (LPEQChild { childPc = pc,
                                        , childVars = Set.fromList (pc:vidDecls)
                                        , childBody = body })
               Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      (TxsDefs.view -> Guard g bexpr) ->
          do child <- getLinearizedChild bexpr
             lpeqGuard currentBExpr [child]
      (TxsDefs.view -> Choice bexprs) ->
          do children <- Monad.mapM linearizeRecursive (Set.toList bexprs)
             lpeqChoice currentBExpr children
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do children <- Monad.mapM linearizeRecursive bexprs
             lpeqParallel currentBExpr children
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do child <- getLinearizedChild bexpr
             lpeqHide currentBExpr [child]
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do child1 <- getLinearizedChild bexpr1
             child2 <- getLinearizedChild bexpr2
             lpeqEnable currentBExpr [child1, child2]
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do child1 <- getLinearizedChild bexpr1
             child2 <- getLinearizedChild bexpr2
             lpeqDisable currentBExpr [child1, child2]
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do child1 <- getLinearizedChild bexpr1
             child2 <- getLinearizedChild bexpr2
             lpeqInterrupt currentBExpr [child1, child2]
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do child <- getLinearizedChild bexpr
             lpeqActionPref currentBExpr [child]
      (TxsDefs.view -> ValueEnv venv bexpr) ->
          error ("ValueEnv should have been eliminated by now (\"" ++ show currentBExpr ++ "\")!")
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldParProcMaps soFar (map actoffer transitions)
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- addProgCounters


