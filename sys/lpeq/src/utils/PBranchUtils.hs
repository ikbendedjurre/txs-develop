{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  PBranchUtils
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module PBranchUtils (
PBranchLinearizer,
isPBranch,
isLinearBranch,
isLinearBExpr,
checkLinearBExpr,
checkLinearBExprs,
extractProcInstData,
module BranchUtils
) where

import qualified Data.List as List
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified ProcDef
import qualified VarId
import BehExprDefs
import ProcIdFactory
import BranchUtils

import ProcSearch

type PBranchLinearizer  = ([TxsDefs.VExpr] -> TxsDefs.BExpr)                -- Function for the construction of a recursive process instantiation.
                       -> TxsDefs.VExpr                                     -- Guard that must hold for the non-linear branch to be enabled.
                       -> TxsDefs.BExpr                                     -- Non-linear branch.
                       -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])    -- New branches, and the parameters required by those branches.
-- PBranchLinearizer

-- Checks if the given expression is a branch that contains a parallel structure (Parallel, Enable, Disable, or Interrupt).
isPBranch :: TxsDefs.BExpr -> Bool
isPBranch currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide _cidSet bexpr) -> checkInnerExpr bexpr
      _ -> checkInnerExpr currentBExpr
  where
    checkInnerExpr :: TxsDefs.BExpr -> Bool
    checkInnerExpr innerExpr =
        case innerExpr of
          (TxsDefs.view -> ActionPref _actOffer bexpr) ->
              case bexpr of
                (TxsDefs.view -> ProcInst {}) -> False
                _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
          (TxsDefs.view -> Guard _g bexpr) ->
              case bexpr of
                (TxsDefs.view -> Parallel {}) -> True
                (TxsDefs.view -> Enable {}) -> True
                (TxsDefs.view -> Disable {}) -> True
                (TxsDefs.view -> Interrupt {}) -> True
                _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
          _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
    -- checkInnerExpr
-- isPBranch

-- Checks if the given branch is linear.
-- This includes checking if the process instantiation is recursive.
-- If the branch is NOT linear, messages are returned to explain why.
isLinearBranch :: ProcId.ProcId -> TxsDefs.BExpr -> [String]
isLinearBranch expectedPid currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide _cidSet bexpr) -> checkInnerExpr bexpr
      _ -> checkInnerExpr currentBExpr
  where
    checkInnerExpr :: TxsDefs.BExpr -> [String]
    checkInnerExpr innerExpr =
        case innerExpr of
          (TxsDefs.view -> ActionPref _actOffer bexpr) ->
              case bexpr of
                (TxsDefs.view -> ProcInst pid _ _) ->
                    if pid /= expectedPid
                    then ["Expected " ++ TxsShow.fshow expectedPid ++ " but found " ++ TxsShow.fshow pid ++ "!"]
                    else []
                _ -> ["ProcInst expected but found " ++ TxsShow.fshow innerExpr]
          _ -> ["ActionPref expected but found " ++ TxsShow.fshow innerExpr]
    -- checkInnerExpr
-- isLinearBranch

-- Checks if the given expression is linear.
-- Same as 'isLinearBranch', but can also handle Choice expressions
-- (all members of a Choice expression should be linear).
isLinearBExpr :: ProcId.ProcId -> TxsDefs.BExpr -> [String]
isLinearBExpr expectedPid bexpr = concatMap (isLinearBranch expectedPid) (Set.toList (getBranches bexpr))

-- Checks if the given expression is linear.
-- If not, it prints debug information (input, output, and problems that were found).
checkLinearBExpr :: ProcId.ProcId -> [TxsDefs.BExpr] -> TxsDefs.BExpr -> IOC.IOC ()
checkLinearBExpr expectedPid preLinearizationBExprs postLinearizationBExpr = do
    case isLinearBExpr expectedPid postLinearizationBExpr of
      [] -> return ()
      msgs -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO "Linearization failure (1/4) ~~ Inputs:" ]
                 Monad.mapM_ (printProcsInBExpr "Input::") preLinearizationBExprs
                 IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO "Linearization failure (2/4) ~~ Output:" ]
                 printProcsInBExpr "Output::" postLinearizationBExpr
                 IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("Linearization failure (3/4) ~~ Problems:\n" ++ List.intercalate "\n" msgs) ]
                 error "Linearization failure (4/4) ~~ End!"
-- checkLinearBExpr

-- Checks if the given expressions are all linear.
-- If not, it prints debug information (input, output, and problems that were found).
checkLinearBExprs :: ProcId.ProcId -> [TxsDefs.BExpr] -> [TxsDefs.BExpr] -> IOC.IOC ()
checkLinearBExprs expectedPid preLinearizationBExprs = Monad.mapM_ (checkLinearBExpr expectedPid preLinearizationBExprs)

extractProcInstData :: TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [(VarId.VarId, TxsDefs.VExpr)])
extractProcInstData (TxsDefs.view -> ProcInst pid _ vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls vidDecls body) -> do
          return (getBranches body, zip vidDecls vexprs)
      Nothing -> error ("Unknown process (\"" ++ showProcId pid ++ "\")!")
extractProcInstData currentBExpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

















