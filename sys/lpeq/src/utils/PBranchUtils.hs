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
extractProcInstBranches,
extractProcInstParamEqs,
ensureFreshVarsInProcInst
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified ProcDef
import qualified VarId
import qualified Subst
import BehExprDefs
import ProcIdFactory
import VarFactory
import ActOfferFactory
import BranchUtils

type PBranchLinearizer = ([TxsDefs.VExpr] -> TxsDefs.BExpr) -> TxsDefs.VExpr -> TxsDefs.BExpr -> IOC.IOC (TxsDefs.BExpr, Set.Set TxsDefs.BExpr, [VarId.VarId])

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

extractProcInstBranches :: TxsDefs.BExpr -> IOC.IOC ([VarId.VarId], Set.Set TxsDefs.BExpr)
extractProcInstBranches (TxsDefs.view -> ProcInst pid _ vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls vidDecls body) -> do
          let subst = Subst.subst (Map.fromList (zip vidDecls vexprs)) Map.empty
          return (vidDecls, getBranches (subst body))
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
extractProcInstBranches currentBExpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

extractProcInstParamEqs :: TxsDefs.BExpr -> IOC.IOC (Map.Map VarId.VarId TxsDefs.VExpr)
extractProcInstParamEqs (TxsDefs.view -> ProcInst pid _ vexprs) = do
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef _cidDecls vidDecls _body) -> do
          return (Map.fromList (zip vidDecls vexprs))
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
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
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
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




