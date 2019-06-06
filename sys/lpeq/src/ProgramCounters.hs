{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProgramCounters
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ProgramCounters (
addProgramCounters
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

addProgramCounters :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
addProgramCounters = addProgCounters Set.empty

addProgCounters :: Set.Set ProcId.ProcId -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
addProgCounters beenHere currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          do let newProcInst = procInst pid cids (ValExpr.cstrConst (Constant.Cint 0):vexprs)
             if Set.member pid beenHere
             then return newProcInst
             else do r <- getProcById pid
                     case r of
                       Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
                           pcDecl <- createFreshIntVarFromPrefix "pc"
                           tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
                           let newPDef = ProcDef.ProcDef cidDecls (pcDecl:vidDecls) body
                           let tdefs' = tdefs { TxsDefs.procDefs = Map.insert pid newPDef (TxsDefs.procDefs tdefs) }
                           IOC.modifyCS (\st -> st { IOC.tdefs = tdefs' })
                           return currentBExpr
                       Nothing -> return newProcInst
      (TxsDefs.view -> Guard g bexpr) ->
          do bexpr' <- addProgCounters beenHere bexpr
             return (guard g bexpr')
      (TxsDefs.view -> Choice bexprs) ->
          do bexprs' <- Set.fromList <$> Monad.mapM (addProgCounters beenHere) (Set.toList bexprs)
             return (choice bexprs')
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do bexprs' <- Monad.mapM (addProgCounters beenHere) bexprs
             return (parallel cidSet bexprs')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do bexpr' <- addProgCounters beenHere bexpr
             return (hide cidSet bexpr')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do bexpr1' <- addProgCounters beenHere bexpr1
             bexpr2' <- addProgCounters beenHere bexpr2
             return (enable bexpr1' acceptOffers bexpr2')
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do bexpr1' <- addProgCounters beenHere bexpr1
             bexpr2' <- addProgCounters beenHere bexpr2
             return (disable bexpr1' bexpr2')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do bexpr1' <- addProgCounters beenHere bexpr1
             bexpr2' <- addProgCounters beenHere bexpr2
             return (interrupt bexpr1' bexpr2')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do bexpr' <- addProgCounters beenHere bexpr
             return (actionPref actOffer bexpr')
      (TxsDefs.view -> ValueEnv venv bexpr) ->
          do bexpr' <- addProgCounters beenHere bexpr
             return (valueEnv venv bexpr')
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldParProcMaps soFar (map actoffer transitions)
      _ -> return (error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"))
-- addProgCounters


