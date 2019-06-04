{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcessReachability
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ProcessReachability (
ReachableProcMap,
getReachableProcMap
) where

import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ProcId
import qualified ProcDef
import BehExprDefs
import ProcIdFactory

type ReachableProcMap = Map.Map ProcId.ProcId ProcDef.ProcDef

getReachableProcMap :: TxsDefs.BExpr -> IOC.IOC (Either [String] ReachableProcMap)
getReachableProcMap = getProcesses (Right Map.empty)

getProcesses :: Either [String] ReachableProcMap -> TxsDefs.BExpr -> IOC.IOC (Either [String] ReachableProcMap)
getProcesses soFar@(Left _) _ = return soFar
getProcesses soFar@(Right m) currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do if Map.member pid m
             then return soFar
             else do r <- getProcById pid
                     case r of
                       Just (pdef@(ProcDef.ProcDef _cids _vids body)) -> getProcesses (Right (Map.insert pid pdef m)) body
                       Nothing -> return (Left ["Could not find process definition (\"" ++ show pid ++ "\")!"])
      (TxsDefs.view -> Guard _guard bexpr) ->
          getProcesses soFar bexpr
      (TxsDefs.view -> Choice bexprs) ->
          foldProcesses soFar bexprs
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          foldProcesses soFar bexprs
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          getProcesses soFar bexpr
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          foldProcesses soFar [bexpr1, bexpr2]
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          foldProcesses soFar [bexpr1, bexpr2]
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          foldProcesses soFar [bexpr1, bexpr2]
      (TxsDefs.view -> ActionPref _offer bexpr) ->
          getProcesses soFar bexpr
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          getProcesses soFar bexpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldProcesses soFar (map actoffer transitions)
      _ -> return (Left ["Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"])
-- getProcesses

foldProcesses :: Foldable t => Either [String] ReachableProcMap -> t TxsDefs.BExpr -> IOC.IOC (Either [String] ReachableProcMap)
foldProcesses = Monad.foldM getProcesses

