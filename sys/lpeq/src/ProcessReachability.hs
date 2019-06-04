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
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ProcId
import qualified ProcDef
import BehExprDefs
import ProcIdFactory

type ReachableProcMap = Map.Map ProcId.ProcId Int
type ParProcMap = (ReachableProcMap, [ProcId.ProcId], Set.Set ProcId.ProcId)

getReachableProcMap :: TxsDefs.BExpr -> IOC.IOC (Either [String] ReachableProcMap)
getReachableProcMap startBExpr = do
    r <- getParProcMap (Right (Map.empty, [], Set.empty)) startBExpr
    case r of
      Left msgs -> return (Left msgs)
      Right (m, _, _) -> return (Right m)
-- getReachableProcMap

getParProcMap :: Either [String] ParProcMap -> TxsDefs.BExpr -> IOC.IOC (Either [String] ParProcMap)
getParProcMap soFar@(Left _) _ = return soFar
getParProcMap soFar@(Right (m, parProcStack, branchPids)) currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do if elem pid parProcStack
             then return (Left ["Unable to handle recursive parallelization (\"" ++ show pid ++ "\")!"])
             else if Set.member pid branchPids
                  then return soFar
                  else do r <- getProcById pid
                          case r of
                            Just (ProcDef.ProcDef _cids _vids body) -> do
                                let m' = Map.insert pid (Map.findWithDefault 0 pid m + 1) m
                                let parProcStack' = if Set.null branchPids then pid:parProcStack else parProcStack
                                getParProcMap (Right (m', parProcStack', Set.insert pid branchPids)) body
                            Nothing -> return (Left ["Could not find process definition (\"" ++ show pid ++ "\")!"])
      (TxsDefs.view -> Guard _guard bexpr) ->
          getParProcMap soFar bexpr
      (TxsDefs.view -> Choice bexprs) ->
          foldParProcMaps soFar bexprs
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          foldParProcMaps (Right (m, parProcStack, Set.empty)) bexprs
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          getParProcMap soFar bexpr
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          foldParProcMaps soFar [bexpr1, bexpr2]
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          foldParProcMaps soFar [bexpr1, bexpr2]
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          foldParProcMaps soFar [bexpr1, bexpr2]
      (TxsDefs.view -> ActionPref _offer bexpr) ->
          getParProcMap soFar bexpr
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          getParProcMap soFar bexpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldParProcMaps soFar (map actoffer transitions)
      _ -> return (Left ["Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"])
-- getParProcMap

foldParProcMaps :: Foldable t => Either [String] ParProcMap -> t TxsDefs.BExpr -> IOC.IOC (Either [String] ParProcMap)
foldParProcMaps = Monad.foldM getParProcMap

