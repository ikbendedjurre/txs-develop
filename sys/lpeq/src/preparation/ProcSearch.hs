{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcSearch
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ProcSearch (
getProcsInBExpr
) where

import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ProcDef
import BehExprDefs
import ProcIdFactory

-- Lists all processes that can be reached from the given behavioral expression.
-- Works by depth-first-search.
getProcsInBExpr :: TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.ProcId)
getProcsInBExpr = searchBExprForProcs Set.empty

searchBExprForProcs :: Set.Set TxsDefs.ProcId -> TxsDefs.BExpr -> IOC.IOC (Set.Set TxsDefs.ProcId)
searchBExprForProcs soFar currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do if Set.member pid soFar
             then return soFar
             else do r <- getProcById pid
                     case r of
                       Just (ProcDef.ProcDef _cidDecls _vidDecls body) -> do
                           searchBExprForProcs (Set.insert pid soFar) body
                       Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      (TxsDefs.view -> Guard _g bexpr) ->
          do searchBExprForProcs soFar bexpr
      (TxsDefs.view -> Choice bexprs) ->
          do Monad.foldM searchBExprForProcs soFar (Set.toList bexprs)
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          do Monad.foldM searchBExprForProcs soFar bexprs
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          do searchBExprForProcs soFar bexpr
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          do soFar' <- searchBExprForProcs soFar bexpr1
             searchBExprForProcs soFar' bexpr2
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do soFar' <- searchBExprForProcs soFar bexpr1
             searchBExprForProcs soFar' bexpr2
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do soFar' <- searchBExprForProcs soFar bexpr1
             searchBExprForProcs soFar' bexpr2
      (TxsDefs.view -> ActionPref _actOffer bexpr) ->
          do searchBExprForProcs soFar bexpr
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          do searchBExprForProcs soFar bexpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- searchBExprForProcs


