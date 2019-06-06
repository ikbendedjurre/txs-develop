{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcDepTree
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ProcDepTree (
ProcDepTree(..),
getProcDepTree
) where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ProcId
import qualified ProcDef
import BehExprDefs
import ProcIdFactory

data ProcDepTree = ProcDepTree (Maybe ProcId.ProcId) (Set.Set ProcDepTree) deriving (Eq, Ord)

emptyTree :: ProcDepTree
emptyTree = ProcDepTree Nothing Set.empty

leaf :: ProcId.ProcId -> ProcDepTree
leaf pid = ProcDepTree (Just pid) Set.empty

showProcDepTree :: String -> String -> ProcDepTree -> [String]
showProcDepTree pidPrefix depsPrefix (ProcDepTree maybePid dependencies) =
    let pidStrs = [pidPrefix ++ showMaybePid maybePid] in
      if Set.null dependencies
      then pidStrs
      else let depsList = Set.toList dependencies in
           let depsStrs = concatMap (showProcDepTree (depsPrefix ++ "|-") (depsPrefix ++ "| ")) (List.init depsList) in
           let lastStrs = showProcDepTree (depsPrefix ++ "\\-") (depsPrefix ++ "  ") (List.last depsList) in
             pidStrs ++ depsStrs ++ lastStrs
  where
    showMaybePid :: Maybe ProcId.ProcId -> String
    showMaybePid (Just pid) = Text.unpack (ProcId.name pid)
    showMaybePid Nothing = "ROOT"
-- showProcDepTree

instance Show ProcDepTree where
    show = List.intercalate "\n" . showProcDepTree "" ""
-- Show ProcDepTree

-- Local helper type. Parameters are:
--  1. The dependency tree that has been constructed so far.
--  2. The branch/process stack:
--       We depend on PBranchInst having been applied.
--       Therefore, each parallel branch is a process instantiation.
--       When searching a branch, we do not want to see the same process being instantiated again (= circular dependency).
--  3. The dependency tree that is currently being constructed (a new tree is started for every branch).
type TreeBuildState = (ProcDepTree, [ProcId.ProcId], Set.Set ProcId.ProcId, [String])

-- Builds the process dependency tree for a given behavioral expression.
-- Depends on PBranchInst having been applied first.
getProcDepTree :: TxsDefs.BExpr -> IOC.IOC (Either [String] ProcDepTree)
getProcDepTree startBExpr = do
    (tree, _, _, msgs) <- buildTree (ProcDepTree Nothing Set.empty, [], Set.empty, []) startBExpr
    if List.null msgs
    then return (Right tree)
    else return (Left (msgs ++ ["Process dependency tree:"] ++ showProcDepTree "" "" tree))
-- getProcDepTree

buildTree :: TreeBuildState -> TxsDefs.BExpr -> IOC.IOC TreeBuildState
buildTree buildState@(ProcDepTree maybePid dependencies, bpStack, inProgress, msgs) currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do -- Detect (and avoid) infinite recursion:
             if List.elem pid bpStack
             then return (ProcDepTree maybePid dependencies, bpStack, inProgress, msgs ++ ["Recursive parallelization => Circular dependency => Cannot be linearized (\"" ++ show pid ++ "\")!"])
             else -- Avoid infinite recursion within the same branch:
                  if Set.member pid inProgress
                  then return buildState
                  else do r <- getProcById pid
                          case r of
                            Just (ProcDef.ProcDef _cids _vids body) ->
                                case maybePid of
                                  -- This is the first process instantiation of the current branch, and so
                                  -- we adopt the process id as the 'owner' of the branch:
                                  Nothing -> buildTree (ProcDepTree (Just pid) Set.empty, pid:bpStack, Set.singleton pid, msgs) body
                                  -- There already is a process that owns the current branch.
                                  -- The process that is called, is a dependency of that process:
                                  Just _ -> do let dependencies' = Set.insert (leaf pid) dependencies
                                               buildTree (ProcDepTree maybePid dependencies', bpStack, Set.insert pid inProgress, msgs) body
                            Nothing -> return (ProcDepTree maybePid dependencies, bpStack, inProgress, msgs ++ ["Could not find process definition (\"" ++ show pid ++ "\")!"])
      (TxsDefs.view -> Guard _guard bexpr) ->
          buildTree buildState bexpr
      (TxsDefs.view -> ActionPref _offer bexpr) ->
          buildTree buildState bexpr
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          buildTree buildState bexpr
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          buildTree buildState bexpr
      (TxsDefs.view -> Choice bexprs) ->
          if Set.null bexprs
          then return buildState
          else Monad.foldM buildTree buildState (Set.toList bexprs)
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          if List.null bexprs
          then return (ProcDepTree maybePid dependencies, bpStack, inProgress, msgs ++ ["Parallel expression without sub-expressions (\"" ++ show currentBExpr ++ "\")!"])
          else addParallelDependencies buildState bexprs
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          addParallelDependencies buildState [bexpr1, bexpr2]
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          addParallelDependencies buildState [bexpr1, bexpr2]
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          addParallelDependencies buildState [bexpr1, bexpr2]
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldParProcMaps soFar (map actoffer transitions)
      _ -> return (ProcDepTree maybePid dependencies, bpStack, inProgress, msgs ++ ["Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"])
-- buildTree

addParallelDependencies :: TreeBuildState -> [TxsDefs.BExpr] -> IOC.IOC TreeBuildState
addParallelDependencies (ProcDepTree maybePid dependencies, bpStack, inProgress, msgs) bexprs = do
    rs <- Monad.mapM (buildTree (emptyTree, bpStack, Set.empty, [])) bexprs
    let dependencies' = Set.union dependencies (Set.fromList (map getBuildStateTree rs))
    let msgs' = msgs ++ concatMap getBuildStateMsgs rs
    return (ProcDepTree maybePid dependencies', bpStack, inProgress, msgs')
  where
    getBuildStateTree :: TreeBuildState -> ProcDepTree
    getBuildStateTree (tree, _, _, _) = tree
    
    getBuildStateMsgs :: TreeBuildState -> [String]
    getBuildStateMsgs (_, _, _, ms) = ms
-- addParallelDependencies

