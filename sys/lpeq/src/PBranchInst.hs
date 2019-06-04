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
import BehExprDefs
import ProcIdFactory
import ConcatEither
import qualified Scopes
import qualified VarEnv

doPBranchInst :: TxsDefs.BExpr -> IOC.IOC (Either [String] TxsDefs.BExpr)
doPBranchInst startBExpr = do
    r <- lookForPBranches Scopes.empty startBExpr
    case r of
      Left msgs -> return (Left msgs)
      Right (bexpr, _exit) -> return (Right bexpr) -- Maybe check if EXIT has correct type?
-- doPBranchInst

lookForPBranches :: Scopes.Scope -> TxsDefs.BExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, ProcId.ExitSort))
lookForPBranches scope currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do r <- concatEither <$> Monad.mapM (instPBranch scope) bexprs
             case r of
               Left msgs -> return (Left (concat msgs))
               Right rs -> if allTheSame (map snd rs)
                           then return (Right (parallel (Scopes.applyToChanSet scope cidSet) (map fst rs), snd (head rs)))
                           else return (Left ["Inconsistent EXIT signatures (\"" ++ show currentBExpr ++ "\")!"])
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          return (Right (procInst pid (Scopes.applyToChans scope cids) (Scopes.applyToVExprs scope vexprs), ProcId.procexit pid))
      (TxsDefs.view -> Guard g bexpr) ->
          do r <- lookForPBranchesInMultiple scope [bexpr]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr']) -> return (Right (guard (Scopes.applyToVExpr scope' g) bexpr', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Choice bexprs) ->
          do r <- lookForPBranchesInMultiple scope (Set.toList bexprs)
             case r of
               Left msgs -> return (Left msgs)
               Right (_scope', exit', bexprs') -> return (Right (choice (Set.fromList bexprs'), exit'))
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do r <- lookForPBranchesInMultiple scope [bexpr]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr']) -> return (Right (hide (Scopes.applyToChanSet scope' cidSet) bexpr', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do r <- lookForPBranchesInMultiple scope [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr1', bexpr2']) -> return (Right (enable bexpr1' (map (Scopes.applyToChanOffer scope') acceptOffers) bexpr2', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do r <- lookForPBranchesInMultiple scope [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right (_scope', exit', [bexpr1', bexpr2']) -> return (Right (disable bexpr1' bexpr2', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do r <- lookForPBranchesInMultiple scope [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right (_scope', exit', [bexpr1', bexpr2']) -> return (Right (interrupt bexpr1' bexpr2', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do r <- lookForPBranchesInMultiple scope [bexpr]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr']) -> return (Right (actionPref (Scopes.applyToActOffer scope' actOffer) bexpr', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> ValueEnv {}) ->
          instPBranch scope currentBExpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldProcesses soFar (map actoffer transitions)
      _ -> return (Left ["Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"])
  where
    allTheSame :: Eq a => [a] -> Bool
    allTheSame [] = True
    allTheSame [_] = True
    allTheSame (x1:x2:xs) = (x1 == x2) && allTheSame (x2:xs)
-- lookForPBranches

instPBranch :: Scopes.Scope -> TxsDefs.BExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, ProcId.ExitSort))
instPBranch scope currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          return (Right (procInst pid (Scopes.applyToChans scope cids) (Scopes.applyToVExprs scope vexprs), ProcId.procexit pid))
      (TxsDefs.view -> Guard g bexpr) ->
          do r <- lookForPBranchesInMultiple scope [bexpr]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr']) -> do Right <$> regAndInstProc scope' exit' (guard (Scopes.applyToVExpr scope' g) bexpr')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Choice bexprs) ->
          do r <- lookForPBranchesInMultiple scope (Set.toList bexprs)
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', bexprs') -> Right <$> regAndInstProc scope' exit' (choice (Set.fromList bexprs'))
      (TxsDefs.view -> Parallel {}) ->
          lookForPBranches scope currentBExpr
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do r <- lookForPBranchesInMultiple scope [bexpr]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr']) -> do Right <$> regAndInstProc scope' exit' (hide (Scopes.applyToChanSet scope' cidSet) bexpr')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do r <- lookForPBranchesInMultiple scope [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr1', bexpr2']) -> do Right <$> regAndInstProc scope' exit' (enable bexpr1' (map (Scopes.applyToChanOffer scope') acceptOffers) bexpr2')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do r <- lookForPBranchesInMultiple scope [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr1', bexpr2']) -> do Right <$> regAndInstProc scope' exit' (disable bexpr1' bexpr2')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do r <- lookForPBranchesInMultiple scope [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr1', bexpr2']) -> do Right <$> regAndInstProc scope' exit' (interrupt bexpr1' bexpr2')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do r <- lookForPBranchesInMultiple scope [bexpr]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr']) -> do Right <$> regAndInstProc scope' exit' (actionPref (Scopes.applyToActOffer scope' actOffer) bexpr')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> ValueEnv venv bexpr) ->
          do r <- lookForPBranchesInMultiple scope [bexpr]
             case r of
               Left msgs -> return (Left msgs)
               Right (scope', exit', [bexpr']) -> do Right <$> regAndInstProcUsingVarEnv scope' (Map.map (Scopes.applyToVExpr scope) venv) exit' bexpr'
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      -- (TxsDefs.view -> StAut _sid _venv transitions) ->
          -- foldProcesses soFar (map actoffer transitions)
      _ -> return (Left ["Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"])
-- instPBranch

-- Parallel branches are instantiated recursively by this function.
lookForPBranchesInMultiple :: Scopes.Scope -> [TxsDefs.BExpr] -> IOC.IOC (Either [String] (Scopes.Scope, ProcId.ExitSort, [TxsDefs.BExpr]))
lookForPBranchesInMultiple scope bexprs = do
    scope' <- Scopes.cloneScope scope
    rs <- concatEither <$> Monad.mapM (lookForPBranches scope') bexprs
    case rs of
      Left msgs -> return (Left (concat msgs))
      Right bs -> if null bs
                  then return (Right (Scopes.empty, ProcId.NoExit, []))
                  else do let bexprs' = map fst bs
                          let exits' = map snd bs
                          if allTheSame exits'
                          then return (Right (scope', head exits', bexprs'))
                          else return (Left ["Inconsistent EXIT signatures (\"" ++ show bexprs ++ "\")!"])
  where
    allTheSame :: Eq a => [a] -> Bool
    allTheSame [] = True
    allTheSame [_] = True
    allTheSame (x1:x2:xs) = (x1 == x2) && allTheSame (x2:xs)
-- lookForPBranchesInMultiple

-- Creates a process definition from the given scope and body and registers it.
-- It also creates an instantiation of the process, which is returned.
regAndInstProc :: Scopes.Scope -> ProcId.ExitSort -> TxsDefs.BExpr -> IOC.IOC (TxsDefs.BExpr, ProcId.ExitSort)
regAndInstProc scope = regAndInstProcUsingVarEnv scope Map.empty

-- Creates a process definition from the given scope and body and registers it.
-- It also creates an instantiation of the process, which is returned.
regAndInstProcUsingVarEnv :: Scopes.Scope -> VarEnv.VEnv -> ProcId.ExitSort -> TxsDefs.BExpr -> IOC.IOC (TxsDefs.BExpr, ProcId.ExitSort)
regAndInstProcUsingVarEnv scope venv exit body = do
    let cids = Map.toList (Scopes.chanMap scope)
    let vids = Map.toList (Scopes.varMap scope)
    let assignments = Map.toList venv
    let newProcParams = map snd vids ++ map fst assignments
    newPid <- createFreshProcIdFromChansAndVars (Text.pack "Proc") (map snd cids) newProcParams exit
    let newPDef = ProcDef.ProcDef (map snd cids) newProcParams body
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    let tdefs' = tdefs { TxsDefs.procDefs = Map.insert newPid newPDef (TxsDefs.procDefs tdefs) }
    IOC.modifyCS (\st -> st { IOC.tdefs = tdefs' })
    let newProcValues = map (ValExpr.cstrVar . fst) vids ++ map snd assignments
    return (procInst newPid (map fst cids) newProcValues, exit)
-- regAndInstProcUsingVarEnv


