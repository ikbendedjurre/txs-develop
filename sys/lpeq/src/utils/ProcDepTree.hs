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
getProcDepTreeProblems,
getProcDepTree,
getMaxDepthPerProc,
getProcsOrderedByMaxDepth
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified ProcDef
import BehExprDefs
import ProcIdFactory

import ProcSearch
import ThreadUtils

data ProcDepTree = Uninitialized
                 | Branch ProcId.ProcId [ProcDepTree]
                 | Circular ProcId.ProcId
                 | InfiniteLoop ProcId.ProcId
                   deriving (Eq, Ord)
-- ProcDepTree

showProcDepTree :: String -> String -> ProcDepTree -> [String]
showProcDepTree pidPrefix _depsPrefix Uninitialized = [pidPrefix ++ "UNINIT"]
showProcDepTree pidPrefix depsPrefix (Branch ownerPid dependencies) = [pidPrefix ++ TxsShow.fshow ownerPid] ++ showProcDepTreeDeps depsPrefix dependencies
showProcDepTree pidPrefix _depsPrefix (Circular ownerPid) = [pidPrefix ++ "CIRCULAR " ++ TxsShow.fshow ownerPid]
showProcDepTree pidPrefix _depsPrefix (InfiniteLoop ownerPid) = [pidPrefix ++ "INFLOOP " ++ TxsShow.fshow ownerPid]

showProcDepTreeDeps :: String -> [ProcDepTree] -> [String]
showProcDepTreeDeps _depsPrefix [] = []
showProcDepTreeDeps depsPrefix deps =
    let depsStrs = concatMap (showProcDepTree (depsPrefix ++ "|-") (depsPrefix ++ "| ")) (List.init deps) in
    let lastStrs = showProcDepTree (depsPrefix ++ "\\-") (depsPrefix ++ ". ") (List.last deps) in
      depsStrs ++ lastStrs
-- showProcDepTreeDeps

instance Show ProcDepTree where
    show = List.intercalate "\n" . showProcDepTree "" ""
-- Show ProcDepTree

getProcDepTreeProblems :: TxsDefs.BExpr -> IOC.IOC [String]
getProcDepTreeProblems startBExpr = do
    tree <- getProcDepTree startBExpr
    let problems = getProblems tree
    if null problems
    then do procStrs <- showProcsInBExpr startBExpr
            IOC.putInfo (showProcDepTree "" "" tree ++ procStrs)
            return []
    else do let problemsStrs = ["Encountered problems while constructing process dependency tree:"] ++ map ("|-" ++) (List.init problems) ++ ["\\-" ++ List.last problems]
            let treeStrs = "Process dependency tree:" : showProcDepTree "" "" tree
            procStrs <- showProcsInBExpr startBExpr
            return (problemsStrs ++ treeStrs ++ procStrs)
  where
    getProblems :: ProcDepTree -> [String]
    getProblems Uninitialized = ["Tree contains uninitialized branches!"]
    getProblems (Branch _ dependencies) = concatMap getProblems dependencies
    getProblems (Circular pid) = ["Circular dependency related to process " ++ TxsShow.fshow pid ++ "!"]
    getProblems (InfiniteLoop pid) = ["Process calls to process " ++ TxsShow.fshow pid ++ " that are not separated by any action!"]
-- getProcDepTree

-- Builds the process dependency tree for a given behavioral expression.
-- Depends on PBranchInst having been applied first.
getProcDepTree :: TxsDefs.BExpr -> IOC.IOC ProcDepTree
getProcDepTree currentBExpr = head <$> getParTrees (Nothing, Set.empty, Set.empty, Set.empty) currentBExpr

type Visited = ( Maybe ProcId.ProcId
               , Set.Set ProcId.ProcId
               , Set.Set ProcId.ProcId
               , Set.Set ProcId.ProcId
               )
-- Visited

getSeqTrees :: Visited -> TxsDefs.BExpr -> IOC.IOC [ProcDepTree]
getSeqTrees visited@(parentParProc, parProcs, seqProcs, seqProcsAfterAct) currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs)
            -- Detect (and avoid) infinite recursion:
          | Set.member pid parProcs -> return [Circular pid]
          | Set.member pid seqProcs -> return [InfiniteLoop pid]
          | Set.member pid seqProcsAfterAct -> return []
          | otherwise -> do r <- getProcById pid
                            case r of
                              Just (ProcDef.ProcDef _cids _vids body) ->
                                  getSeqTrees (parentParProc, parProcs, Set.insert pid seqProcs, seqProcsAfterAct) body
                              Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      (TxsDefs.view -> Choice bexprs) ->
          concat <$> Monad.mapM (getSeqTrees visited) (Set.toList bexprs)
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          concat <$> Monad.mapM (getParTrees visited) bexprs
      (TxsDefs.view -> Guard _guard bexpr) ->
          getTrees currentBExpr 0 visited bexpr
      (TxsDefs.view -> ActionPref _offer bexpr) ->
          getTrees currentBExpr 0 (parentParProc, parProcs, Set.empty, Set.union seqProcsAfterAct seqProcs) bexpr
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          getTrees currentBExpr 0 visited bexpr
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          getBinTrees bexpr1 bexpr2
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          getBinTrees bexpr1 bexpr2
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          getBinTrees bexpr1 bexpr2
      _ -> error ("Behavioral expression not anticipated (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
  where
    getBinTrees :: TxsDefs.BExpr -> TxsDefs.BExpr -> IOC.IOC [ProcDepTree]
    getBinTrees bexpr1 bexpr2 = do
        trees1 <- getTrees currentBExpr 0 visited bexpr1
        trees2 <- getTrees currentBExpr 1 visited bexpr2
        return (trees1 ++ trees2)
    -- getBinTrees
-- getSeqTrees

getParTrees :: Visited -> TxsDefs.BExpr -> IOC.IOC [ProcDepTree]
getParTrees (parentParProc, parProcs, seqProcs, seqProcsAfterAct) currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs)
            -- Detect (and avoid) infinite recursion:
          | Set.member pid parProcs -> return [Circular pid]
          | Set.member pid seqProcs -> return [InfiniteLoop pid]
          | Set.member pid seqProcsAfterAct -> return [Uninitialized]
          | otherwise -> do r <- getProcById pid
                            case r of
                              Just (ProcDef.ProcDef _cids _vids body) -> do
                                  let parProcs' = case parentParProc of
                                                    Just ppp -> Set.insert ppp parProcs
                                                    Nothing -> Set.empty
                                  seqTrees <- getSeqTrees (Just pid, parProcs', Set.singleton pid, Set.empty) body
                                  return [Branch pid seqTrees]
                              Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      _ -> error ("Behavioral expression not anticipated (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
-- getParTrees

getTrees :: TxsDefs.BExpr -> Int -> Visited -> TxsDefs.BExpr -> IOC.IOC [ProcDepTree]
getTrees currentBExpr subExprIndex =
    case getSubExprType currentBExpr subExprIndex of
      StpSequential -> getSeqTrees
      _ -> getParTrees
-- getTrees

-- buildTree :: ProcDepTree -> [ProcId.ProcId] -> Set.Set ProcId.ProcId -> Set.Set ProcId.ProcId -> TxsDefs.BExpr -> IOC.IOC ProcDepTree
-- buildTree tree@(Circular _) _ _ _ _ = error ("Should not be extending a circular tree (\"" ++ show tree ++ "\")!")
-- buildTree tree@(InfiniteLoop _) _ _ _ _ = error ("Should not be extending an infinite-loop tree (\"" ++ show tree ++ "\")!")
-- buildTree tree pbStack sbSetPostAct sbSet currentBExpr =
    -- case currentBExpr of
      -- (TxsDefs.view -> ProcInst pid _cids _vexprs)
            -- -- Detect (and avoid) infinite recursion:
          -- | pid `List.elem` pbStack -> return (Circular pid)
          -- | Set.member pid sbSetPostAct -> return tree
          -- | Set.member pid sbSet -> return (addBranch tree pbStack (InfiniteLoop pid))
          -- | otherwise -> do r <- getProcById pid
                            -- case r of
                              -- Just (ProcDef.ProcDef _cids _vids body) ->
                                  -- case tree of
                                    -- (Branch ownerPid dependencies) -> buildTree (Branch ownerPid dependencies) pbStack sbSetPostAct (Set.insert pid sbSet) body
                                    -- -- This is the first process instantiation of the current branch (_ can only be Uninitialized), and so
                                    -- -- we adopt the process id as the 'owner' of the branch:
                                    -- _ -> buildTree (Branch pid []) pbStack Set.empty (Set.singleton pid) body
                              -- Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      -- (TxsDefs.view -> Choice bexprs) ->
          -- if Set.null bexprs
          -- then return tree
          -- else do rs <- Monad.mapM (buildTree tree pbStack sbSetPostAct sbSet) (Set.toList bexprs)
                  -- return (foldl mergeTrees tree rs)
      -- (TxsDefs.view -> Parallel _cidSet bexprs) ->
          -- if List.null bexprs
          -- then return tree
          -- else addDependencies tree pbStack bexprs
      
      -- (TxsDefs.view -> Guard _guard bexpr) ->
          -- buildTree tree pbStack sbSetPostAct sbSet bexpr
      -- (TxsDefs.view -> ActionPref _offer bexpr) ->
          -- buildTree tree pbStack (Set.union sbSetPostAct sbSet) Set.empty bexpr
      -- (TxsDefs.view -> Hide _cidSet bexpr) ->
          -- buildTree tree pbStack sbSetPostAct sbSet bexpr
      
      -- (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) -> do
          -- tree' <- addDependencies tree pbStack [bexpr1]
          -- buildTree tree' pbStack sbSetPostAct sbSet bexpr2
      -- (TxsDefs.view -> Disable bexpr1 bexpr2) -> do
          -- -- addDependencies tree pbStack [bexpr1, bexpr2]
          -- tree' <- buildTree tree pbStack sbSetPostAct sbSet bexpr1
          -- buildTree tree' pbStack sbSetPostAct sbSet bexpr2
      -- (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          -- addDependencies tree pbStack [bexpr1, bexpr2]
      -- _ -> error ("Behavioral expression not anticipated (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
-- -- buildTree

-- handleSubExpr :: TxsDefs.BExpr -> Int -> ProcDepTree -> [ProcId.ProcId] -> TxsDefs.BExpr -> IOC.IOC ProcDepTree
-- handleSubExpr currentBExpr subExprIndex = if isThreadSubExpr currentBExpr subExprIndex then addDependency else searchForDependencies

-- addDependency :: ProcDepTree -> [ProcId.ProcId] -> TxsDefs.BExpr -> IOC.IOC ProcDepTree
-- addDependency Uninitialized (prevOwnerPid:pbStack) bexpr = Branch prevOwnerPid [addition]
    -- buildTree Uninitialized (prevOwnerPid:pbStack) Set.empty Set.empty
    
-- addBranch (Branch ownerPid dependencies) _pbStack addition = Branch ownerPid (dependencies ++ [addition])
-- addDependency parent pbStack currentBExpr =
    -- buildTree Uninitialized (parentPid:pbStack) Set.empty Set.empty
-- -- addDependency

-- searchForDependencies :: ProcDepTree -> [ProcId.ProcId] -> TxsDefs.BExpr -> IOC.IOC ProcDepTree
-- searchForDependencies parent pbStack currentBExpr =
    
-- -- searchForDependencies

-- mergeTrees :: ProcDepTree -> ProcDepTree -> ProcDepTree
-- mergeTrees t1@(Branch pid1 deps1) t2@(Branch pid2 deps2) =
    -- if pid1 == pid2
    -- then Branch pid1 (deps1 ++ deps2)
    -- else error ("Cannot merge trees with different owners (left = " ++ show t1 ++ "; right = " ++ show t2 ++ ")!")
-- mergeTrees t1 t2 = error ("Cannot merge trees (left = " ++ show t1 ++ "; right = " ++ show t2 ++ ")!")
-- -- mergeTrees

-- addBranch :: ProcDepTree -> [ProcId.ProcId] -> ProcDepTree -> ProcDepTree
-- addBranch Uninitialized (prevOwnerPid:_pbStack) addition = Branch prevOwnerPid [addition]
-- addBranch (Branch ownerPid dependencies) _pbStack addition = Branch ownerPid (dependencies ++ [addition])
-- addBranch t _ _ = error ("Should not be adding branch to this tree (\"" ++ show t ++ "\")!")


-- addDependencies :: ProcDepTree -> [ProcId.ProcId] -> [TxsDefs.BExpr] -> IOC.IOC ProcDepTree
-- addDependencies Uninitialized (prevOwnerPid:pbStack) bexprs = do
    -- deps <- getDependencies prevOwnerPid pbStack bexprs
    -- return (Branch prevOwnerPid deps)
-- addDependencies (Branch ownerPid dependencies) pbStack bexprs = do
    -- deps <- getDependencies ownerPid pbStack bexprs
    -- return (Branch ownerPid (deps ++ dependencies))
-- addDependencies t _ _ = error ("Should not be adding dependencies to this tree (\"" ++ show t ++ "\")!")
-- -- addDependencies

-- getDependencies :: ProcId.ProcId -> [ProcId.ProcId] -> [TxsDefs.BExpr] -> IOC.IOC [ProcDepTree]
-- getDependencies parentPid pbStack bexprs = do
    -- rs <- Monad.mapM (buildTree Uninitialized (parentPid:pbStack) Set.empty Set.empty) bexprs
    -- return (filter (Uninitialized /=) rs)
-- -- getDependencies

getMaxDepthPerProc :: ProcDepTree -> Map.Map ProcId.ProcId Int
getMaxDepthPerProc tree = snd (dfs tree)
  where
    dfs :: ProcDepTree -> (Int, Map.Map ProcId.ProcId Int)
    dfs (Branch ownerPid []) = (0, Map.singleton ownerPid 0)
    dfs (Branch ownerPid dependencies) = let (a, b) = foldl f (0, Map.empty) dependencies in (a + 1, Map.insert ownerPid (a + 1) b)
    dfs _ = (0, Map.empty)
    
    f :: (Int, Map.Map ProcId.ProcId Int) -> ProcDepTree -> (Int, Map.Map ProcId.ProcId Int)
    f soFar t = let (tdepth, tmap) = dfs t in (max (fst soFar) (tdepth + 1), Map.unionWith max (snd soFar) tmap)
-- getMaxDepthPerProc

getProcsOrderedByMaxDepth :: ProcDepTree -> [ProcId.ProcId]
getProcsOrderedByMaxDepth tree = map fst (List.sortOn snd (Map.toList (getMaxDepthPerProc tree)))



