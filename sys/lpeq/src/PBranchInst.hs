{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  PBranchInst
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module PBranchInst (
doPBranchInst
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ValExpr
import qualified ProcId
import qualified ProcDef
import qualified ChanId
import BehExprDefs
import ProcIdFactory
import qualified Scopes

-- Recursively identifies parallel sub-expressions in a given behavioral expression, and
-- creates process definitions for each of those sub-expressions (including program counters).
-- Sub-expressions are replaced by instantiations of corresponding process definitions.
-- 
-- (Next, a dependency tree will be inferred from the process definitions.)
-- 
-- The given behavioral expression should be closed except for channels, which must be provided as well.
doPBranchInst :: [ChanId.ChanId] -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
doPBranchInst allChanIds startBExpr = do
    (bexpr, _exit) <- instPBranch (Scopes.fromChans allChanIds) startBExpr
    return bexpr -- Maybe check if EXIT has correct type?
-- doPBranchInst

-- Searches a given expression for parallel sub-expressions.
lookForPBranch :: Scopes.Scope -> TxsDefs.BExpr -> IOC.IOC (TxsDefs.BExpr, ProcId.ExitSort)
lookForPBranch scope currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          return (procInst pid (Scopes.applyToChans scope cids) (Scopes.applyToVExprs scope vexprs), ProcId.procexit pid)
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do (bexprs', exit') <- forAllBExprs (instPBranch scope) bexprs
             return (parallel (Scopes.applyToChanSet scope cidSet) bexprs', exit')
      (TxsDefs.view -> Guard g bexpr) ->
          do (bexpr', exit') <- lookForPBranch scope bexpr
             return (guard (Scopes.applyToVExpr scope g) bexpr', exit')
      (TxsDefs.view -> Choice bexprs) ->
          do (bexprs', exit') <- forAllBExprs (lookForPBranch scope) (Set.toList bexprs)
             return (choice (Set.fromList bexprs'), exit')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do (bexpr', exit') <- lookForPBranch scope bexpr
             return (hide (Scopes.applyToChanSet scope cidSet) bexpr', exit')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do (bexpr1', _) <- instPBranch scope bexpr1
             (bexpr2', exit') <- instPBranch (Scopes.addChanOffers scope acceptOffers) bexpr2
             return (enable bexpr1' (map (Scopes.applyToChanOffer scope) acceptOffers) bexpr2', exit')
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do (bexpr1', _) <- instPBranch scope bexpr1
             (bexpr2', exit') <- instPBranch scope bexpr2
             return (disable bexpr1' bexpr2', exit')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do (bexpr1', _) <- instPBranch scope bexpr1
             (bexpr2', exit') <- instPBranch scope bexpr2
             return (interrupt bexpr1' bexpr2', exit')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do let scope' = Scopes.addActOffer scope actOffer
             (bexpr', exit') <- instPBranch scope' bexpr
             return (actionPref (Scopes.applyToActOffer scope' actOffer) bexpr', exit')
      (TxsDefs.view -> ValueEnv _venv _bexpr) ->
           error ("ValExpr should have already been rewritten (\"" ++ show currentBExpr ++ "\")!")
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- lookForPBranch

instPBranch :: Scopes.Scope -> TxsDefs.BExpr -> IOC.IOC (TxsDefs.BExpr, ProcId.ExitSort)
instPBranch scope currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          -- Already is a process instantiation:
          return (procInst pid (Scopes.applyToChans scope cids) (Scopes.applyToVExprs scope vexprs), ProcId.procexit pid)
      (TxsDefs.view -> Guard g bexpr) ->
          do scope' <- Scopes.cloneScope scope
             (bexpr', exit') <- lookForPBranch scope' bexpr
             regAndInstProc scope' exit' (guard (Scopes.applyToVExpr scope' g) bexpr')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do scope' <- Scopes.cloneScope scope
             let scope'' = Scopes.addActOffer scope' actOffer
             (bexpr', exit') <- lookForPBranch scope'' bexpr
             regAndInstProc scope' exit' (actionPref (Scopes.applyToActOffer scope'' actOffer) bexpr')
      (TxsDefs.view -> ValueEnv _venv _bexpr) ->
          error ("ValExpr should have already been rewritten (\"" ++ show currentBExpr ++ "\")!")
      (TxsDefs.view -> Choice bexprs) ->
          do scope' <- Scopes.cloneScope scope
             (bexprs', exit') <- forAllBExprs (lookForPBranch scope') (Set.toList bexprs)
             regAndInstProc scope' exit' (choice (Set.fromList bexprs'))
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do scope' <- Scopes.cloneScope scope
             (bexpr', exit') <- lookForPBranch scope' bexpr
             regAndInstProc scope' exit' (hide (Scopes.applyToChanSet scope' cidSet) bexpr')
       -- Parallel expression can contain parallel sub-expressions:
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do scope' <- Scopes.cloneScope scope
             (bexprs', exit') <- forAllBExprs (instPBranch scope') bexprs
             regAndInstProc scope' exit' (parallel (Scopes.applyToChanSet scope' cidSet) bexprs')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do scope1 <- Scopes.cloneScope scope
             (bexpr1', _) <- instPBranch scope1 bexpr1
             let scope2 = Scopes.addChanOffers scope1 acceptOffers
             (bexpr2', exit') <- instPBranch scope2 bexpr2
             regAndInstProc scope1 exit' (enable bexpr1' (map (Scopes.applyToChanOffer scope2) acceptOffers) bexpr2')
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do scope' <- Scopes.cloneScope scope
             (bexpr1', _) <- instPBranch scope' bexpr1
             (bexpr2', exit') <- instPBranch scope' bexpr2
             regAndInstProc scope' exit' (disable bexpr1' bexpr2')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do scope' <- Scopes.cloneScope scope
             (bexpr1', _) <- instPBranch scope' bexpr1
             (bexpr2', exit') <- instPBranch scope' bexpr2
             regAndInstProc scope' exit' (interrupt bexpr1' bexpr2')
      -- (TxsDefs.view -> StAut _sid _venv transitions) ->
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- instPBranch

-- Multiple branches are evaluated in the same manner with this function.
forAllBExprs :: (TxsDefs.BExpr -> IOC.IOC (TxsDefs.BExpr, ProcId.ExitSort)) -> [TxsDefs.BExpr] -> IOC.IOC ([TxsDefs.BExpr], ProcId.ExitSort)
forAllBExprs f bexprs = do
    rs <- Monad.mapM f bexprs
    if null rs
    then return ([], ProcId.NoExit)
    else return (map fst rs, last (map snd rs))
-- forAllBExprs

-- Creates a process definition from the given scope and body and registers it.
-- It also creates an instantiation of the process, which is returned.
regAndInstProc :: Scopes.Scope -> ProcId.ExitSort -> TxsDefs.BExpr -> IOC.IOC (TxsDefs.BExpr, ProcId.ExitSort)
regAndInstProc scope exit body = do
    let cids = Map.toList (Scopes.chanMap scope)
    let vids = Map.toList (Scopes.varMap scope)
    let newProcParams = map snd vids
    newPid <- createFreshProcIdFromChansAndVars (Text.pack "Proc") (map snd cids) newProcParams exit
    let newPDef = ProcDef.ProcDef (map snd cids) newProcParams body
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    let tdefs' = tdefs { TxsDefs.procDefs = Map.insert newPid newPDef (TxsDefs.procDefs tdefs) }
    IOC.modifyCS (\st -> st { IOC.tdefs = tdefs' })
    let newProcValues = map (ValExpr.cstrVar . fst) vids
    return (procInst newPid (map fst cids) newProcValues, exit)
-- regAndInstProcUsingVarEnv

