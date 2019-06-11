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
-- import qualified EnvData
import qualified TxsDefs
import qualified ProcId
import qualified ProcDef
import BehExprDefs
import ProcIdFactory
import ConcatEither
import UntilFixedPoint

data ProcDepTree = Uninitialized
                 | Branch ProcId.ProcId (Set.Set ProcDepTree)
                 | Circular ProcId.ProcId
                   deriving (Eq, Ord)
-- ProcDepTree

showProcDepTree :: String -> String -> ProcDepTree -> [String]
showProcDepTree pidPrefix depsPrefix Uninitialized = [pidPrefix ++ "UNINIT"]
showProcDepTree pidPrefix depsPrefix (Branch ownerPid dependencies) =
    let pidStrs = [pidPrefix ++ Text.unpack (ProcId.name ownerPid)] in
      if Set.null dependencies
      then pidStrs
      else let depsList = Set.toList dependencies in
           let depsStrs = concatMap (showProcDepTree (depsPrefix ++ "|-") (depsPrefix ++ "| ")) (List.init depsList) in
           let lastStrs = showProcDepTree (depsPrefix ++ "\\-") (depsPrefix ++ ". ") (List.last depsList) in
             pidStrs ++ depsStrs ++ lastStrs
showProcDepTree pidPrefix depsPrefix (Circular ownerPid) = [pidPrefix ++ "CIRCULAR " ++ Text.unpack (ProcId.name ownerPid)]

instance Show ProcDepTree where
    show = List.intercalate "\n" . showProcDepTree "" ""
-- Show ProcDepTree

-- Local helper type. Parameters are:
--  1. The dependency tree that has been constructed so far.
--  2. The branch/process stack:
--       We depend on PBranchInst having been applied.
--       Therefore, each parallel branch is a process instantiation.
--       When searching a branch, we do not want to see the same process being instantiated again (= circular dependency).
--  3. Error messages.
type TreeBuildState = (ProcDepTree, [ProcId.ProcId], Set.Set ProcId.ProcId)

-- Builds the process dependency tree for a given behavioral expression.
-- Depends on PBranchInst having been applied first.
getProcDepTree :: TxsDefs.BExpr -> IOC.IOC (Either [String] ProcDepTree)
getProcDepTree startBExpr = do
    (tree, _, _) <- buildTree (Uninitialized, [], Set.empty) startBExpr
    -- if List.null msgs
    -- then return (Right tree)
    -- else return (Left (msgs ++ ["Process dependency tree:"] ++ showProcDepTree "" "" tree))
    return (Left (["Process dependency tree:"] ++ showProcDepTree "" "" tree))
-- getProcDepTree

buildTree :: TreeBuildState -> TxsDefs.BExpr -> IOC.IOC TreeBuildState
buildTree (Uninitialized, pbStack, sbSet) currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do -- Detect (and avoid) infinite recursion:
             if List.elem pid pbStack
             then return (Circular pid, pbStack, sbSet)
             else do r <- getProcById pid
                     case r of
                       Just (ProcDef.ProcDef _cids _vids body) ->
                           -- This is the first process instantiation of the current branch, and so
                           -- we adopt the process id as the 'owner' of the branch:
                           buildTree (Branch pid Set.empty, pbStack, Set.singleton pid) body
      _ -> error ("Process instantiation expected, found \"" ++ show currentBExpr ++ "\"!")
-- [Uninitialized]
buildTree buildState@(Branch ownerPid dependencies, pbStack, sbSet) currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do -- Detect (and avoid) infinite recursion:
             if List.elem pid pbStack
             then return (Circular pid, pbStack, sbSet)
             else do if Set.member pid dependencies
                     then return (Branch pid, pbStack, sbSet)
                     else do r <- getProcById pid
                             case r of
                               Just (ProcDef.ProcDef _cids _vids body) ->
                                   buildTree (Branch ownerPid dependencies, pbStack, Set.insert pid sbSet) body
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
          then return (ProcDepTree maybePid reachablePids dependencies, pbStack, sbSet)
          else addDependencies buildState currentBExpr bexprs
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          addDependencies buildState currentBExpr [bexpr1, bexpr2]
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          addDependencies buildState currentBExpr [bexpr1, bexpr2]
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          addDependencies buildState currentBExpr [bexpr1, bexpr2]
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- [[Branch]]
buildTree buildState _ = error ("Illegal build state (\"" ++ show buildState ++ "\")!")
-- [[Circular]]

addDependencies :: TreeBuildState -> TxsDefs.BExpr -> [TxsDefs.BExpr] -> IOC.IOC TreeBuildState
addDependencies (Uninitialized, pbStack, sbSet) currentBExpr bexprs = error ("[INTERNAL ERROR] Branch does not have an owner (stack = " ++ show bpStack ++ ", expr = " ++ show currentBExpr ++ ")!")
addDependencies (Branch ownerId dependencies, bpStack, sbSet) _currentBExpr bexprs = do
    -- Here, we add the process that owns the branch to the process/branch stack
    -- so that we can detect infinite recursion:
    rs <- Monad.mapM (buildTree (Uninitialized, pid:bpStack, Set.empty)) bexprs
    let dependencies' = Set.union dependencies (Set.fromList (map getBuildStateTree rs))
    return (Branch ownerId dependencies', bpStack, sbSet)
  where
    getBuildStateTree :: TreeBuildState -> ProcDepTree
    getBuildStateTree (tree, _, _) = tree
-- addDependencies
addDependencies buildState _currentBExpr _bexprs = error ("Illegal build state (\"" ++ show buildState ++ "\")!")

