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
import qualified VarEnv
import BehExprDefs
import ProcIdFactory
import ConcatEither
import qualified Scopes

-- Recursively identifies parallel sub-expressions in a given behavioral expression, and
-- creates process definitions for each of those sub-expressions (including program counters).
-- Sub-expressions are replaced by instantiations of corresponding process definitions.
-- 
-- (Later, a dependency tree will be inferred for the process definitions.)
-- 
-- The given behavioral expression should be closed except for channels, which must be provided as well.
doPBranchInst :: Set.Set ChanId.ChanId -> TxsDefs.BExpr -> IOC.IOC (Either [String] TxsDefs.BExpr)
doPBranchInst cids startBExpr = do
    r <- instPBranch (Scopes.fromChans cids) startBExpr
    case r of
      Left msgs -> return (Left msgs)
      Right (bexpr, _exit) -> return (Right bexpr) -- Maybe check if EXIT has correct type?
-- doPBranchInst

-- Searches a given expression for parallel sub-expressions.
lookForPBranch :: Scopes.Scope -> TxsDefs.BExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, ProcId.ExitSort))
lookForPBranch scope currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          return (Right (procInst pid (Scopes.applyToChans scope cids) (Scopes.applyToVExprs scope vexprs), ProcId.procexit pid))
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do r <- forAllBExprs (instPBranch scope) bexprs
             case r of
               Left msgs -> return (Left msgs)
               Right (bexprs', exit') -> return (Right (parallel (Scopes.applyToChanSet scope cidSet) bexprs', exit'))
      (TxsDefs.view -> Guard g bexpr) ->
          do r <- lookForPBranch scope bexpr
             case r of
               Left msgs -> return (Left msgs)
               Right (bexpr', exit') -> return (Right (guard (Scopes.applyToVExpr scope g) bexpr', exit'))
      (TxsDefs.view -> Choice bexprs) ->
          do r <- forAllBExprs (lookForPBranch scope) (Set.toList bexprs)
             case r of
               Left msgs -> return (Left msgs)
               Right (bexprs', exit') -> return (Right (choice (Set.fromList bexprs'), exit'))
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do r <- lookForPBranch scope bexpr
             case r of
               Left msgs -> return (Left msgs)
               Right (bexpr', exit') -> return (Right (hide (Scopes.applyToChanSet scope cidSet) bexpr', exit'))
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do r <- forAllBExprs (instPBranch scope) [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right ([bexpr1', bexpr2'], exit') -> return (Right (enable bexpr1' (map (Scopes.applyToChanOffer scope) acceptOffers) bexpr2', exit')) -- TODO exit values are not (always) correct!
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do r <- forAllBExprs (instPBranch scope) [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right ([bexpr1', bexpr2'], exit') -> return (Right (disable bexpr1' bexpr2', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do r <- forAllBExprs (instPBranch scope) [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right ([bexpr1', bexpr2'], exit') -> return (Right (interrupt bexpr1' bexpr2', exit'))
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do r <- lookForPBranch scope bexpr
             case r of
               Left msgs -> return (Left msgs)
               Right (bexpr', exit') -> return (Right (actionPref (Scopes.applyToActOffer scope actOffer) bexpr', exit'))
      (TxsDefs.view -> ValueEnv {}) ->
          instPBranch scope currentBExpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldProcesses soFar (map actoffer transitions)
      _ -> return (Left ["Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"])
-- lookForPBranch

instPBranch :: Scopes.Scope -> TxsDefs.BExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, ProcId.ExitSort))
instPBranch scope currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          -- Already is a process instantiation:
          return (Right (procInst pid (Scopes.applyToChans scope cids) (Scopes.applyToVExprs scope vexprs), ProcId.procexit pid))
      (TxsDefs.view -> Guard g bexpr) ->
          do scope' <- Scopes.cloneScope scope
             r <- lookForPBranch scope' bexpr
             case r of
               Left msgs -> return (Left msgs)
               Right (bexpr', exit') -> do Right <$> regAndInstProc scope' exit' (guard (Scopes.applyToVExpr scope' g) bexpr')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do scope' <- Scopes.cloneScope scope
             r <- lookForPBranch scope' bexpr
             case r of
               Left msgs -> return (Left msgs)
               Right (bexpr', exit') -> do Right <$> regAndInstProc scope' exit' (actionPref (Scopes.applyToActOffer scope' actOffer) bexpr')
      (TxsDefs.view -> ValueEnv venv bexpr) ->
          do scope' <- Scopes.cloneScope scope
             r <- lookForPBranch scope' bexpr
             case r of
               Left msgs -> return (Left msgs)
               Right (bexpr', exit') -> do Right <$> regAndInstProcUsingVarEnv scope' (Map.map (Scopes.applyToVExpr scope') venv) exit' bexpr'
      (TxsDefs.view -> Choice bexprs) ->
          do scope' <- Scopes.cloneScope scope
             r <- forAllBExprs (lookForPBranch scope') (Set.toList bexprs)
             case r of
               Left msgs -> return (Left msgs)
               Right (bexprs', exit') -> Right <$> regAndInstProc scope' exit' (choice (Set.fromList bexprs'))
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do scope' <- Scopes.cloneScope scope
             r <- lookForPBranch scope' bexpr
             case r of
               Left msgs -> return (Left msgs)
               Right (bexpr', exit') -> do Right <$> regAndInstProc scope' exit' (hide (Scopes.applyToChanSet scope' cidSet) bexpr')
       -- Parallel expression can also contain parallel expressions:
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do scope' <- Scopes.cloneScope scope
             r <- forAllBExprs (instPBranch scope') bexprs
             case r of
               Left msgs -> return (Left msgs)
               Right (bexprs', exit') -> do Right <$> regAndInstProc scope' exit' (parallel (Scopes.applyToChanSet scope' cidSet) bexprs')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do scope' <- Scopes.cloneScope scope
             r <- forAllBExprs (instPBranch scope') [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right ([bexpr1', bexpr2'], exit') -> do Right <$> regAndInstProc scope' exit' (enable bexpr1' (map (Scopes.applyToChanOffer scope') acceptOffers) bexpr2')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do scope' <- Scopes.cloneScope scope
             r <- forAllBExprs (instPBranch scope') [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right ([bexpr1', bexpr2'], exit') -> do Right <$> regAndInstProc scope' exit' (disable bexpr1' bexpr2')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do scope' <- Scopes.cloneScope scope
             r <- forAllBExprs (instPBranch scope') [bexpr1, bexpr2]
             case r of
               Left msgs -> return (Left msgs)
               Right ([bexpr1', bexpr2'], exit') -> do Right <$> regAndInstProc scope' exit' (interrupt bexpr1' bexpr2')
               _ -> return (Left ["Output not accounted for (\"" ++ show r ++ "\")!"])
      -- (TxsDefs.view -> StAut _sid _venv transitions) ->
          -- foldProcesses soFar (map actoffer transitions)
      _ -> return (Left ["Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"])
-- instPBranch

-- Multiple branches are evaluated in the same manner with this function.
forAllBExprs :: (TxsDefs.BExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, ProcId.ExitSort))) -> [TxsDefs.BExpr] -> IOC.IOC (Either [String] ([TxsDefs.BExpr], ProcId.ExitSort))
forAllBExprs f bexprs = do
    rs <- Monad.mapM f bexprs
    case concatEither rs of
      Left msgs -> return (Left (concat msgs))
      Right bs -> if null bs
                  then return (Right ([], ProcId.NoExit))
                  else do let bexprs' = map fst bs
                          let exits' = map snd bs
                          if allTheSame exits'
                          then return (Right (bexprs', head exits'))
                          else return (Left ["Inconsistent EXIT signatures (\"" ++ show bexprs ++ "\")!"])
  where
    allTheSame :: Eq a => [a] -> Bool
    allTheSame [] = True
    allTheSame [_] = True
    allTheSame (x1:x2:xs) = (x1 == x2) && allTheSame (x2:xs)
-- forAllBExprs

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


