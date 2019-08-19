{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  BranchLinearityUtils
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module BranchLinearityUtils (
TExprLinResult(..),
TExprLinearizer,
isNonLinearBranch,
isLinearBranch,
isLinearBExpr,
checkLinearBExpr,
checkLinearBExprs,
extractProcInstData,
extractParamEqs,
module BranchUtils
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified ProcDef
import qualified VarId
import BehExprDefs
import ProcIdFactory
import BranchUtils

import ProcSearch

data TExprLinResult = TExprLinResult { lrBranches :: Set.Set TxsDefs.BExpr                        -- New branches.
                                     , lrParams :: [VarId.VarId]                                  -- Parameters required by those branches (in order).
                                     , lrPredefInits :: Map.Map VarId.VarId TxsDefs.VExpr         -- Initial values of parameters (if necessary).
                                     , lrStopValues :: Map.Map VarId.VarId TxsDefs.VExpr          -- Parameters can be set to these values in order to stop the process.
                                     }
-- TExprLinResult

type TExprLinearizer   =  ([TxsDefs.VExpr] -> TxsDefs.BExpr)                                 -- Function for the construction of a recursive process instantiation.
                       -> TxsDefs.VExpr                                                      -- Guard that must hold for the non-linear branch to be enabled.
                       -> TxsDefs.BExpr                                                      -- Non-linear branch.
                       -> IOC.IOC TExprLinResult
-- PBranchLinearizer

-- Checks if the given expression is a branch that contains a parallel structure (Parallel, Enable, Disable, or Interrupt).
isNonLinearBranch :: TxsDefs.BExpr -> Bool
isNonLinearBranch currentBExpr =
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
-- isNonLinearBranch

-- Checks if the given branch is linear.
-- This includes checking if the process instantiation is recursive.
-- If the branch is NOT linear, messages are returned to explain why.
isLinearBranch :: (TxsDefs.BExpr -> Bool) -> ProcId.ProcId -> TxsDefs.BExpr -> [String]
isLinearBranch exceptionFunc expectedPid currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide _cidSet bexpr) -> checkInnerExpr bexpr
      _ -> checkInnerExpr currentBExpr
  where
    checkInnerExpr :: TxsDefs.BExpr -> [String]
    checkInnerExpr innerExpr =
        if exceptionFunc innerExpr
        then []
        else case innerExpr of
               (TxsDefs.view -> ActionPref _actOffer bexpr) ->
                   case bexpr of
                     (TxsDefs.view -> ProcInst pid _ _) -> ["Expected " ++ TxsShow.fshow expectedPid ++ " but found " ++ TxsShow.fshow pid ++ "!" | pid /= expectedPid]
                     _ -> ["ProcInst expected but found " ++ TxsShow.fshow innerExpr]
               _ -> ["ActionPref expected but found " ++ TxsShow.fshow innerExpr]
    -- checkInnerExpr
-- isLinearBranch

-- Checks if the given expression is linear.
-- Same as 'isLinearBranch', but can also handle Choice expressions
-- (all members of a Choice expression should be linear).
isLinearBExpr :: (TxsDefs.BExpr -> Bool) -> ProcId.ProcId -> TxsDefs.BExpr -> [String]
isLinearBExpr exceptionFunc expectedPid bexpr = concatMap (isLinearBranch exceptionFunc expectedPid) (Set.toList (getBranches bexpr))

-- Checks if the given expression is linear.
-- If not, it prints debug information (input, output, and problems that were found).
checkLinearBExpr :: (TxsDefs.BExpr -> Bool) -> ProcId.ProcId -> [TxsDefs.BExpr] -> TxsDefs.BExpr -> IOC.IOC ()
checkLinearBExpr exceptionFunc expectedPid preLinearizationBExprs postLinearizationBExpr =
    case isLinearBExpr exceptionFunc expectedPid postLinearizationBExpr of
      [] -> return ()
      msgs -> do IOC.putInfo [ "Linearization failure (1/4) ~~ Inputs:" ]
                 Monad.mapM_ (printProcsInBExpr "Input::") preLinearizationBExprs
                 IOC.putInfo [ "Linearization failure failure (2/4) ~~ Output:" ]
                 printProcsInBExpr "Output::" postLinearizationBExpr
                 IOC.putInfo [ "Linearization failure failure (3/4) ~~ Problems:" ]
                 IOC.putInfo msgs
                 IOC.putInfo [ "Linearization failure (4/4) ~~ End!" ]
                 error ("Linearization failure!")
-- checkLinearBExpr

-- Checks if the given expressions are all linear.
-- If not, it prints debug information (input, output, and problems that were found).
checkLinearBExprs :: (TxsDefs.BExpr -> Bool) -> ProcId.ProcId -> [TxsDefs.BExpr] -> [TxsDefs.BExpr] -> IOC.IOC ()
checkLinearBExprs exceptionFunc expectedPid preLinearizationBExprs = Monad.mapM_ (checkLinearBExpr exceptionFunc expectedPid preLinearizationBExprs)

extractProcInstData :: TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [(VarId.VarId, TxsDefs.VExpr)])
extractProcInstData (TxsDefs.view -> ProcInst pid _ vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls vidDecls body) ->
          return (getBranches body, zip vidDecls vexprs)
      Nothing -> error ("Unknown process (\"" ++ showProcId pid ++ "\")!")
extractProcInstData currentBExpr = error ("Behavioral expression not anticipated (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

extractParamEqs :: TxsDefs.BExpr -> IOC.IOC (Map.Map VarId.VarId TxsDefs.VExpr)
extractParamEqs (TxsDefs.view -> ProcInst pid _ vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls vidDecls _body) ->
          return (Map.fromList (zip vidDecls vexprs))
      Nothing -> error ("Unknown process (\"" ++ showProcId pid ++ "\")!")
extractParamEqs currentBExpr = error ("Behavioral expression not anticipated (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")















