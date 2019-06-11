{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcCopy
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ProcCopy (
replaceProcsInBExpr
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ProcDef
import BehExprDefs
import ProcIdFactory

import ProcSearch

-- Creates copies of all processes reachable from the given behavioral expression.
-- Updates process instantiations (in the copies) accordingly.
-- Returns the original behavioral expression in which process instantiations have been updated.
replaceProcsInBExpr :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
replaceProcsInBExpr bexpr = do
    procIds <- getProcsInBExpr bexpr
    freshPidPerPid <- Monad.mapM clonePid (Set.toList procIds)
    let freshPidMap = Map.fromList freshPidPerPid
    Monad.mapM_ (doProc freshPidMap) freshPidPerPid
    replacePidsInBExpr freshPidMap bexpr
  where
    clonePid :: TxsDefs.ProcId -> IOC.IOC (TxsDefs.ProcId, TxsDefs.ProcId)
    clonePid pid = do
        freshPid <- createFreshProcIdFromProcId pid
        return (pid, freshPid)
    -- clonePid
    
    doProc :: Map.Map TxsDefs.ProcId TxsDefs.ProcId -> (TxsDefs.ProcId, TxsDefs.ProcId) -> IOC.IOC ()
    doProc freshPidMap (pid, freshPid) = do
        r <- getProcById pid
        case r of
          Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
              body' <- replacePidsInBExpr freshPidMap body
              registerProc freshPid (ProcDef.ProcDef cidDecls vidDecls body')
          Nothing -> return ()
    -- doProc
-- replaceProcsInBExpr

replacePidsInBExpr :: Map.Map TxsDefs.ProcId TxsDefs.ProcId -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
replacePidsInBExpr freshPidMap currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          do return (procInst (freshPidMap Map.! pid) cids vexprs)
      (TxsDefs.view -> Guard g bexpr) ->
          do bexpr' <- replacePidsInBExpr freshPidMap bexpr
             return (guard g bexpr')
      (TxsDefs.view -> Choice bexprs) ->
          do bexprs' <- Set.fromList <$> Monad.mapM (replacePidsInBExpr freshPidMap) (Set.toList bexprs)
             return (choice bexprs')
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do bexprs' <- Monad.mapM (replacePidsInBExpr freshPidMap) bexprs
             return (parallel cidSet bexprs')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do bexpr' <- replacePidsInBExpr freshPidMap bexpr
             return (hide cidSet bexpr')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do bexpr1' <- replacePidsInBExpr freshPidMap bexpr1
             bexpr2' <- replacePidsInBExpr freshPidMap bexpr2
             return (enable bexpr1' acceptOffers bexpr2')
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do bexpr1' <- replacePidsInBExpr freshPidMap bexpr1
             bexpr2' <- replacePidsInBExpr freshPidMap bexpr2
             return (disable bexpr1' bexpr2')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do bexpr1' <- replacePidsInBExpr freshPidMap bexpr1
             bexpr2' <- replacePidsInBExpr freshPidMap bexpr2
             return (interrupt bexpr1' bexpr2')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do bexpr' <- replacePidsInBExpr freshPidMap bexpr
             return (actionPref actOffer bexpr')
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          do replacePidsInBExpr freshPidMap bexpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- replacePidsInBExpr


