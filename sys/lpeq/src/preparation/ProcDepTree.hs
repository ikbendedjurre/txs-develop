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
getProcDepTree,
getMaxDepthPerProc,
getProcsOrderedByMaxDepth
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified ProcDef
import qualified SortId
import qualified ChanId
import qualified VarId
import BehExprDefs
import ProcIdFactory

import ProcSearch

data ProcDepTree = Uninitialized
                 | Branch ProcId.ProcId [ProcDepTree]
                 | Circular ProcId.ProcId
                 | InfiniteLoop ProcId.ProcId
                   deriving (Eq, Ord)
-- ProcDepTree

showProcDepTree :: String -> String -> ProcDepTree -> [String]
showProcDepTree pidPrefix _depsPrefix Uninitialized = [pidPrefix ++ "UNINIT"]
showProcDepTree pidPrefix depsPrefix (Branch ownerPid dependencies) =
    let pidStrs = [pidPrefix ++ Text.unpack (ProcId.name ownerPid)] in
      if null dependencies
      then pidStrs
      else let depsStrs = concatMap (showProcDepTree (depsPrefix ++ "|-") (depsPrefix ++ "| ")) (List.init dependencies) in
           let lastStrs = showProcDepTree (depsPrefix ++ "\\-") (depsPrefix ++ ". ") (List.last dependencies) in
             pidStrs ++ depsStrs ++ lastStrs
showProcDepTree pidPrefix _depsPrefix (Circular ownerPid) = [pidPrefix ++ "CIRCULAR " ++ Text.unpack (ProcId.name ownerPid)]
showProcDepTree pidPrefix _depsPrefix (InfiniteLoop ownerPid) = [pidPrefix ++ "INFLOOP " ++ Text.unpack (ProcId.name ownerPid)]

instance Show ProcDepTree where
    show = List.intercalate "\n" . showProcDepTree "" ""
-- Show ProcDepTree

-- Builds the process dependency tree for a given behavioral expression.
-- Depends on PBranchInst having been applied first.
getProcDepTree :: TxsDefs.BExpr -> IOC.IOC (Either [String] ProcDepTree)
getProcDepTree startBExpr = do
    tree <- buildTree Uninitialized [] Set.empty Set.empty startBExpr
    let problems = getProblems tree
    if null problems
    then do let treeStrs = ["Process dependency tree:"] ++ showProcDepTree "" "" tree
            procStrs <- showProcs
            Monad.mapM_ (\m -> IOC.putMsgs [ EnvData.TXS_CORE_ANY m ]) (treeStrs ++ procStrs)
            -- return (Left (treeStrs ++ procStrs))
            return (Right tree)
    else do let problemsStrs = ["Encountered problems while constructing process dependency tree:"] ++ map ("|-" ++) (List.init problems) ++ ["\\-" ++ List.last problems]
            let treeStrs = ["Process dependency tree:"] ++ showProcDepTree "" "" tree
            procStrs <- showProcs
            return (Left (problemsStrs ++ treeStrs ++ procStrs))
  where
    showProcs :: IOC.IOC [String]
    showProcs = do
        procIds <- getProcsInBExpr startBExpr
        strPerProc <- concat <$> Monad.mapM showProc (Set.toList procIds)
        return (["START ::= " ++ TxsShow.fshow startBExpr] ++ strPerProc)
    -- showProcs
    
    showProc :: ProcId.ProcId -> IOC.IOC [String]
    showProc pid = do
        r <- getProcById pid
        case r of
          -- Just (ProcDef.ProcDef _cidDecls _vidDecls body) -> return [Text.unpack (ProcId.name pid) ++ " ::= " ++ TxsShow.fshow body ]
          Just (ProcDef.ProcDef cidDecls vidDecls body) -> return ["PROCDEF " ++ showProcSig pid cidDecls vidDecls ++ " ::=", TxsShow.fshow body, "ENDDEF" ]
          Nothing -> return [ show pid ++ " ::= ???" ]
    -- doProc
    
    showProcSig :: ProcId.ProcId -> [ChanId.ChanId] -> [VarId.VarId] -> String
    showProcSig pid cidDecls vidDecls =
        let nameStr = Text.unpack (ProcId.name pid) in
        let cidDeclsStr = "[" ++ List.intercalate "," (map (Text.unpack . ChanId.name) cidDecls) ++ "]" in
        let vidDeclsStr = "(" ++ List.intercalate "; " (map (\v -> Text.unpack (VarId.name v) ++ " :: " ++ Text.unpack (SortId.name (VarId.varsort v))) vidDecls) ++ ")" in
          nameStr ++ " " ++ cidDeclsStr ++ " " ++ vidDeclsStr
    -- showProcSig
    
    getProblems :: ProcDepTree -> [String]
    getProblems Uninitialized = ["Tree contains uninitialized branches!"]
    getProblems (Branch _ dependencies) = concatMap getProblems dependencies
    getProblems (Circular pid) = ["Circular dependency related to process " ++ Text.unpack (ProcId.name pid) ++ "!"]
    getProblems (InfiniteLoop pid) = ["Process calls to process " ++ Text.unpack (ProcId.name pid) ++ " that are not separated by any action!"]
-- getProcDepTree

buildTree :: ProcDepTree -> [ProcId.ProcId] -> Set.Set ProcId.ProcId -> Set.Set ProcId.ProcId -> TxsDefs.BExpr -> IOC.IOC ProcDepTree
buildTree tree@(Circular _) _ _ _ _ = error ("Should not be extending a circular tree (\"" ++ show tree ++ "\")!")
buildTree tree@(InfiniteLoop _) _ _ _ _ = error ("Should not be extending an infinite-loop tree (\"" ++ show tree ++ "\")!")
buildTree tree pbStack sbSetPostAct sbSet currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do -- Detect (and avoid) infinite recursion:
             if List.elem pid pbStack
             then return (Circular pid)
             else do if Set.member pid sbSetPostAct
                     then return tree
                     else if Set.member pid sbSet
                          then return (addDependency tree pbStack (InfiniteLoop pid))
                          else do r <- getProcById pid
                                  case r of
                                    Just (ProcDef.ProcDef _cids _vids body) ->
                                        case tree of
                                          (Branch ownerPid dependencies) -> buildTree (Branch ownerPid dependencies) pbStack sbSetPostAct (Set.insert pid sbSet) body
                                          -- This is the first process instantiation of the current branch (_ can only be Uninitialized), and so
                                          -- we adopt the process id as the 'owner' of the branch:
                                          _ -> buildTree (Branch pid []) pbStack Set.empty (Set.singleton pid) body
                                    Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      (TxsDefs.view -> Guard _guard bexpr) ->
          buildTree tree pbStack sbSetPostAct sbSet bexpr
      (TxsDefs.view -> ActionPref _offer bexpr) ->
          buildTree tree pbStack (Set.union sbSetPostAct sbSet) Set.empty bexpr
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          buildTree tree pbStack sbSetPostAct sbSet bexpr
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          buildTree tree pbStack sbSetPostAct sbSet bexpr
      (TxsDefs.view -> Choice bexprs) ->
          if Set.null bexprs
          then return tree
          else do rs <- Monad.mapM (buildTree tree pbStack sbSetPostAct sbSet) (Set.toList bexprs)
                  return (foldl mergeTrees tree rs)
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          if List.null bexprs
          then return tree
          else addDependencies tree pbStack bexprs
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          addDependencies tree pbStack [bexpr1, bexpr2]
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          addDependencies tree pbStack [bexpr1, bexpr2]
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          addDependencies tree pbStack [bexpr1, bexpr2]
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
-- buildTree

mergeTrees :: ProcDepTree -> ProcDepTree -> ProcDepTree
mergeTrees t1@(Branch pid1 deps1) t2@(Branch pid2 deps2) =
    if pid1 == pid2
    then Branch pid1 (deps1 ++ deps2)
    else error ("Cannot merge trees with different owners (left = " ++ show t1 ++ "; right = " ++ show t2 ++ ")!")
mergeTrees t1 t2 = error ("Cannot merge trees (left = " ++ show t1 ++ "; right = " ++ show t2 ++ ")!")
-- mergeTrees

addDependency :: ProcDepTree -> [ProcId.ProcId] -> ProcDepTree -> ProcDepTree
addDependency Uninitialized (prevOwnerPid:_pbStack) addition = Branch prevOwnerPid [addition]
addDependency (Branch ownerPid dependencies) _pbStack addition = Branch ownerPid (dependencies ++ [addition])
addDependency t _ _ = error ("Should not be adding dependency to this tree (\"" ++ show t ++ "\")!")

addDependencies :: ProcDepTree -> [ProcId.ProcId] -> [TxsDefs.BExpr] -> IOC.IOC ProcDepTree
addDependencies Uninitialized (prevOwnerPid:pbStack) bexprs = do
    deps <- getDependencies prevOwnerPid pbStack bexprs
    return (Branch prevOwnerPid deps)
addDependencies (Branch ownerPid dependencies) pbStack bexprs = do
    deps <- getDependencies ownerPid pbStack bexprs
    return (Branch ownerPid (deps ++ dependencies))
addDependencies t _ _ = error ("Should not be adding dependencies to this tree (\"" ++ show t ++ "\")!")
-- addDependencies

getDependencies :: ProcId.ProcId -> [ProcId.ProcId] -> [TxsDefs.BExpr] -> IOC.IOC [ProcDepTree]
getDependencies parentPid pbStack bexprs = do
    rs <- Monad.mapM (buildTree Uninitialized (parentPid:pbStack) Set.empty Set.empty) bexprs
    return (filter (Uninitialized /=) rs)
-- getDependencies

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



