{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  VEnvElim
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module VEnvElim (
eliminateVEnvs
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ProcDef
import qualified VarEnv
import qualified Subst
import BehExprDefs
import ProcIdFactory

eliminateVEnvs :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
eliminateVEnvs = elimVEnvs Map.empty

elimVEnvs :: VarEnv.VEnv -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
elimVEnvs currentVEnv currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          do r <- getProcById pid
             case r of
               Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
                   body' <- elimVEnvs currentVEnv body
                   tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
                   let newPDef = ProcDef.ProcDef cidDecls vidDecls body'
                   let tdefs' = tdefs { TxsDefs.procDefs = Map.insert pid newPDef (TxsDefs.procDefs tdefs) }
                   IOC.modifyCS (\st -> st { IOC.tdefs = tdefs' })
                   return (procInst pid cids (map (Subst.subst currentVEnv Map.empty) vexprs))
               Nothing -> return currentBExpr
      (TxsDefs.view -> Guard g bexpr) ->
          do bexpr' <- elimVEnvs currentVEnv bexpr
             return (guard (Subst.subst currentVEnv Map.empty g) bexpr')
      (TxsDefs.view -> Choice bexprs) ->
          do bexprs' <- Set.fromList <$> Monad.mapM (elimVEnvs currentVEnv) (Set.toList bexprs)
             return (choice bexprs')
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do bexprs' <- Monad.mapM (elimVEnvs currentVEnv) bexprs
             return (parallel cidSet bexprs')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do bexpr' <- elimVEnvs currentVEnv bexpr
             return (hide cidSet bexpr')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do bexpr1' <- elimVEnvs currentVEnv bexpr1
             bexpr2' <- elimVEnvs currentVEnv bexpr2
             return (enable bexpr1' acceptOffers bexpr2')
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do bexpr1' <- elimVEnvs currentVEnv bexpr1
             bexpr2' <- elimVEnvs currentVEnv bexpr2
             return (disable bexpr1' bexpr2')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do bexpr1' <- elimVEnvs currentVEnv bexpr1
             bexpr2' <- elimVEnvs currentVEnv bexpr2
             return (interrupt bexpr1' bexpr2')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do bexpr' <- elimVEnvs currentVEnv bexpr
             return (actionPref (doActOffer currentVEnv actOffer) bexpr')
      (TxsDefs.view -> ValueEnv venv bexpr) ->
          do let venv' = Map.map (Subst.subst currentVEnv Map.empty) venv
             -- Note that Map.union is left-biased!
             -- (This means that same-name variables are replaced correctly, assuming that this is even allowed.)
             elimVEnvs (Map.union venv' currentVEnv) bexpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldParProcMaps soFar (map actoffer transitions)
      _ -> return (error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"))
-- elimVEnvs

doActOffer :: VarEnv.VEnv -> TxsDefs.ActOffer -> TxsDefs.ActOffer
doActOffer currentVEnv actOffer = actOffer { TxsDefs.constraint = Subst.subst currentVEnv Map.empty (TxsDefs.constraint actOffer) }

