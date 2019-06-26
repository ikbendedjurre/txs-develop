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
extractProcInstBranches,
extractProcInstParamEqs,
ensureFreshVarsInProcInst,
module BranchUtils
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified ProcId
import qualified ProcDef
import qualified VarId
import qualified Subst
import BehExprDefs
import ProcIdFactory
import VarFactory
import ActOfferFactory
import BranchUtils

import ProcSearch

type PBranchLinearizer = ([TxsDefs.VExpr] -> TxsDefs.BExpr) -> TxsDefs.VExpr -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.BExpr, [VarId.VarId])

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

isLinearBExpr :: ProcId.ProcId -> TxsDefs.BExpr -> [String]
isLinearBExpr expectedPid bexpr = concatMap (isLinearBranch expectedPid) (Set.toList (getBranches bexpr))

checkLinearBExpr :: ProcId.ProcId -> [TxsDefs.BExpr] -> TxsDefs.BExpr -> IOC.IOC ()
checkLinearBExpr expectedPid inputBExprs outputBExpr = do
    case isLinearBExpr expectedPid outputBExpr of
      [] -> return ()
      msgs -> do IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO "Linearization failure (1/4) ~~ Inputs:" ]
                 Monad.mapM_ printProcsInBExpr inputBExprs
                 IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO "Linearization failure (2/4) ~~ Output:" ]
                 printProcsInBExpr outputBExpr
                 IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("Linearization failure (3/4) ~~ Problems:\n" ++ List.intercalate "\n" msgs) ]
                 error "Linearization failure (4/4) ~~ End!"
-- checkLinearBExpr

checkLinearBExprs :: ProcId.ProcId -> [TxsDefs.BExpr] -> [TxsDefs.BExpr] -> IOC.IOC ()
checkLinearBExprs expectedPid inputBExprs = Monad.mapM_ (checkLinearBExpr expectedPid inputBExprs)

-- Retrieves the branches (=summands) of the process that is instantiated in the given behavioral expression.
-- Also retrieves the declared parameters of that process.
extractProcInstBranches :: TxsDefs.BExpr -> IOC.IOC ([VarId.VarId], Set.Set TxsDefs.BExpr)
extractProcInstBranches (TxsDefs.view -> ProcInst pid _ vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls vidDecls body) -> do
          let subst = Subst.subst (Map.fromList (zip vidDecls vexprs)) Map.empty
          return (vidDecls, getBranches (subst body))
      Nothing -> error ("Unknown process (\"" ++ showProcId pid ++ "\")!")
extractProcInstBranches currentBExpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

extractProcInstParamEqs :: TxsDefs.BExpr -> IOC.IOC (Map.Map VarId.VarId TxsDefs.VExpr)
extractProcInstParamEqs (TxsDefs.view -> ProcInst pid _ vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls vidDecls _body) -> do
          return (Map.fromList (zip vidDecls vexprs))
      Nothing -> error ("Unknown process (\"" ++ showProcId pid ++ "\")!")
extractProcInstParamEqs currentBExpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

ensureFreshVarsInProcInst :: TxsDefs.BExpr -> IOC.IOC ()
ensureFreshVarsInProcInst (TxsDefs.view -> ProcInst pid _cids _vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
          subst <- createFreshVars (Set.fromList vidDecls)
          newBranches <- Monad.mapM (ensureFreshVarsInBranch subst) (Set.toList (getBranches body))
          let body' = choice (Set.fromList newBranches)
          registerProc pid (ProcDef.ProcDef cidDecls vidDecls body')
      Nothing -> error ("Unknown process (\"" ++ showProcId pid ++ "\")!")
ensureFreshVarsInProcInst currentBExpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

ensureFreshVarsInBranch :: Map.Map VarId.VarId VarId.VarId -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
ensureFreshVarsInBranch subst currentBExpr = do
    let (nonHiddenBExpr, hiddenChans) = removeHide currentBExpr
    case nonHiddenBExpr of
      (TxsDefs.view -> ActionPref actOffer bexpr) -> do
          let (vizVars, hidVars) = getActOfferVars actOffer
          actOfferSubst <- createFreshVars (Set.union vizVars hidVars)
          let subst' = Map.union actOfferSubst subst
          let actOffer' = replaceVarsInActOffer subst' actOffer
          let bexpr' = Subst.subst (Map.map ValExpr.cstrVar subst') Map.empty bexpr
          let actionPref' = actionPref actOffer' bexpr'
          return (applyHide hiddenChans actionPref')
      _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
-- ensureFreshVarsInBranch




