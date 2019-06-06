{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcCounterValues
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ProcCounterValues (

) where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
-- import qualified EnvData
import qualified TxsDefs
import qualified ProcId
import qualified ProcDef
import BehExprDefs
import ProcIdFactory

import ProcDepTree

type ProcMaxDepthMap = Map.Map ProcId.ProcId Int


addProgramCounters :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
addProgramCounters bexpr = do
    ([bexpr'], _) <- addProgCounters ([], Map.empty) bexpr
    return bexpr'
-- addProgramCounters

addProgCounters :: ([TxsDefs.BExpr], Map.Map ProcId.ProcId ProcId.ProcId) -> TxsDefs.BExpr -> IOC.IOC ([TxsDefs.BExpr], Map.Map ProcId.ProcId ProcId.ProcId)
addProgCounters (prevBExprs, replacedProcs) currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          do case replacedProcs Map.!? pid of
               Just newPid -> return (prevBExprs ++ [procInst newPid cids (ValExpr.cstrConst (Constant.Cint 0):vexprs)], replacedProcs)
               Nothing -> do r <- getProcById pid
                             case r of
                               Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
                                   -- First just modify the signature of the process:
                                   newPid <- createFreshProcIdWithDifferentVars pid (getIntSort:ProcId.procvars pid)
                                   
                                   -- Recurse:
                                   ([body'], replacedProcs') <- addProgCounters ([], Map.insert pid newPid replacedProcs) body
                                   
                                   -- Only now we actually change the definition of the process:
                                   pcDecl <- createFreshIntVarFromPrefix "pc"
                                   let newPDef = ProcDef.ProcDef cidDecls (pcDecl:vidDecls) body'
                                   tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
                                   let tdefs' = tdefs { TxsDefs.procDefs = Map.insert newPid newPDef (Map.delete pid (TxsDefs.procDefs tdefs)) }
                                   IOC.modifyCS (\st -> st { IOC.tdefs = tdefs' })
                                   
                                   -- Return the updated process instantiation:
                                   return (prevBExprs ++ [procInst newPid cids (ValExpr.cstrConst (Constant.Cint 0):vexprs)], replacedProcs')
                               Nothing -> return (prevBExprs ++ [currentBExpr], replacedProcs) -- (Should not happen.)
      (TxsDefs.view -> Guard g bexpr) ->
          do ([bexpr'], replacedProcs') <- addProgCounters ([], replacedProcs) bexpr
             return (prevBExprs ++ [guard g bexpr'], replacedProcs')
      (TxsDefs.view -> Choice bexprs) ->
          do (bexprs', replacedProcs') <- Monad.foldM addProgCounters ([], replacedProcs) (Set.toList bexprs)
             return (prevBExprs ++ [choice (Set.fromList bexprs')], replacedProcs')
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do (bexprs', replacedProcs') <- Monad.foldM addProgCounters ([], replacedProcs) bexprs
             return (prevBExprs ++ [parallel cidSet bexprs'], replacedProcs')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do ([bexpr'], replacedProcs') <- addProgCounters ([], replacedProcs) bexpr
             return (prevBExprs ++ [hide cidSet bexpr'], replacedProcs')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do ([bexpr1', bexpr2'], replacedProcs') <- Monad.foldM addProgCounters ([], replacedProcs) [bexpr1, bexpr2]
             return (prevBExprs ++ [enable bexpr1' acceptOffers bexpr2'], replacedProcs')
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do ([bexpr1', bexpr2'], replacedProcs') <- Monad.foldM addProgCounters ([], replacedProcs) [bexpr1, bexpr2]
             return (prevBExprs ++ [disable bexpr1' bexpr2'], replacedProcs')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do ([bexpr1', bexpr2'], replacedProcs') <- Monad.foldM addProgCounters ([], replacedProcs) [bexpr1, bexpr2]
             return (prevBExprs ++ [interrupt bexpr1' bexpr2'], replacedProcs')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do ([bexpr'], replacedProcs') <- addProgCounters ([], replacedProcs) bexpr
             return (prevBExprs ++ [actionPref actOffer bexpr'], replacedProcs')
      (TxsDefs.view -> ValueEnv venv bexpr) ->
          do ([bexpr'], replacedProcs') <- addProgCounters ([], replacedProcs) bexpr
             return (prevBExprs ++ [valueEnv venv bexpr'], replacedProcs')
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldParProcMaps soFar (map actoffer transitions)
      _ -> return (error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"))
-- addProgCounters

