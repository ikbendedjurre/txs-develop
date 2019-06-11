{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  FlattenedChannels
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module FlattenedChannels (
flattenChannels
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ProcId
import qualified ProcDef
import qualified ChanId
import BehExprDefs
import ProcIdFactory

-- Signature of a process instantiation is expressed with channels on the global (model) level,
-- not with channels on the local (process) level.
type ProcInstSignature = (ProcId.ProcId, [ChanId.ChanId])

-- Rewrites the given behavioral expression so that all of its processes have the same channel signature.
-- Also updates process instantiations, including in the expression that is returned.
flattenChannels :: [ChanId.ChanId] -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
flattenChannels allChanIds bexpr = do
    let idChanMap = Map.fromList (zip allChanIds allChanIds)
    sigs <- getSignatures idChanMap Set.empty bexpr
    freshPidPerSig <- Monad.mapM cloneSig (Set.toList sigs)
    let freshPidMap = Map.fromList freshPidPerSig
    Monad.mapM_ (doProc freshPidMap) freshPidPerSig
    replacePidsInBExpr allChanIds idChanMap freshPidMap bexpr
  where
    cloneSig :: ProcInstSignature -> IOC.IOC (ProcInstSignature, TxsDefs.ProcId)
    cloneSig (pid, cids) = do
        freshPid <- createFreshProcIdWithDifferentChans pid allChanIds
        return ((pid, cids), freshPid)
    -- cloneSig
    
    doProc :: Map.Map ProcInstSignature TxsDefs.ProcId -> (ProcInstSignature, TxsDefs.ProcId) -> IOC.IOC ()
    doProc freshPidMap ((pid, cids), freshPid) = do
        r <- getProcById pid
        case r of
          Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
              body' <- replacePidsInBExpr allChanIds (Map.fromList (zip cidDecls cids)) freshPidMap body
              registerProc freshPid (ProcDef.ProcDef allChanIds vidDecls body')
          Nothing -> return ()
    -- doProc
-- flattenChannels

-- Finds all signatures of process instantiations in the given behavioral expression.
getSignatures :: Map.Map ChanId.ChanId ChanId.ChanId -> Set.Set ProcInstSignature -> TxsDefs.BExpr -> IOC.IOC (Set.Set ProcInstSignature)
getSignatures chanMap soFar currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids _vexprs) ->
          do let sig = (pid, map (chanMap Map.!) cids)
             if Set.member sig soFar
             then return soFar
             else do r <- getProcById pid
                     case r of
                       Just (ProcDef.ProcDef cidDecls _vidDecls body) -> do
                           let chanMap' = Map.fromList (zip cidDecls cids)
                           getSignatures chanMap' (Set.insert sig soFar) body
                       Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      (TxsDefs.view -> Guard _g bexpr) ->
          do getSignatures chanMap soFar bexpr
      (TxsDefs.view -> Choice bexprs) ->
          do Monad.foldM (getSignatures chanMap) soFar (Set.toList bexprs)
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          do Monad.foldM (getSignatures chanMap) soFar bexprs
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          do -- Maybe use information that HIDE gives us...?
             getSignatures chanMap soFar bexpr
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          do soFar' <- getSignatures chanMap soFar bexpr1
             getSignatures chanMap soFar' bexpr2
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do soFar' <- getSignatures chanMap soFar bexpr1
             getSignatures chanMap soFar' bexpr2
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do soFar' <- getSignatures chanMap soFar bexpr1
             getSignatures chanMap soFar' bexpr2
      (TxsDefs.view -> ActionPref _actOffer bexpr) ->
          do getSignatures chanMap soFar bexpr
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          do getSignatures chanMap soFar bexpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- getSignatures

-- This method does not require a Monad; we leave it like this in case that changes.
replacePidsInBExpr :: [ChanId.ChanId] -> Map.Map ChanId.ChanId ChanId.ChanId -> Map.Map ProcInstSignature TxsDefs.ProcId -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
replacePidsInBExpr allChanIds chanMap freshPidMap currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid cids vexprs) ->
          do let sig = (pid, map (chanMap Map.!) cids)
             return (procInst (freshPidMap Map.! sig) allChanIds vexprs)
      (TxsDefs.view -> Guard g bexpr) ->
          do bexpr' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr
             return (guard g bexpr')
      (TxsDefs.view -> Choice bexprs) ->
          do bexprs' <- Set.fromList <$> Monad.mapM (replacePidsInBExpr allChanIds chanMap freshPidMap) (Set.toList bexprs)
             return (choice bexprs')
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do bexprs' <- Monad.mapM (replacePidsInBExpr allChanIds chanMap freshPidMap) bexprs
             return (parallel (Set.map (chanMap Map.!) cidSet) bexprs')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do bexpr' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr
             return (hide (Set.map (chanMap Map.!) cidSet) bexpr')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do bexpr1' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr1
             bexpr2' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr2
             return (enable bexpr1' acceptOffers bexpr2')
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do bexpr1' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr1
             bexpr2' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr2
             return (disable bexpr1' bexpr2')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do bexpr1' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr1
             bexpr2' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr2
             return (interrupt bexpr1' bexpr2')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do bexpr' <- replacePidsInBExpr allChanIds chanMap freshPidMap bexpr
             return (actionPref (doActOffer chanMap actOffer) bexpr')
      (TxsDefs.view -> ValueEnv _venv bexpr) ->
          do replacePidsInBExpr allChanIds chanMap freshPidMap bexpr
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- ...
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- replacePidsInBExpr

doActOffer :: Map.Map ChanId.ChanId ChanId.ChanId -> TxsDefs.ActOffer -> TxsDefs.ActOffer
doActOffer chanMap actOffer =
    actOffer { TxsDefs.offers = Set.map (doOffer chanMap) (TxsDefs.offers actOffer) }
-- doActOffer

doOffer :: Map.Map ChanId.ChanId ChanId.ChanId -> TxsDefs.Offer -> TxsDefs.Offer
doOffer chanMap offer = 
    offer { TxsDefs.chanid = chanMap Map.! TxsDefs.chanid offer }
-- doOffer

