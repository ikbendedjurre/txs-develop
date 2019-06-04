{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ExclamToQuest
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module ExclamToQuest (
exclamToQuest
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ValExpr
import qualified ProcId
import qualified SortOf
import qualified ProcDef
import BehExprDefs
import ProcIdFactory
import VarFactory

exclamToQuest :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
exclamToQuest = exclamToQst Set.empty

exclamToQst :: Set.Set ProcId.ProcId -> TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
exclamToQst beenHere currentBExpr = do
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do if Set.member pid beenHere
             then return currentBExpr
             else do r <- getProcById pid
                     case r of
                       Just (ProcDef.ProcDef cids vids body) -> do
                           body' <- exclamToQst (Set.insert pid beenHere) body
                           tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
                           let newPDef = ProcDef.ProcDef cids vids body'
                           let tdefs' = tdefs { TxsDefs.procDefs = Map.insert pid newPDef (TxsDefs.procDefs tdefs) }
                           IOC.modifyCS (\st -> st { IOC.tdefs = tdefs' })
                           return currentBExpr
                       Nothing -> return currentBExpr
      (TxsDefs.view -> Guard g bexpr) ->
          do bexpr' <- exclamToQst beenHere bexpr
             return (guard g bexpr')
      (TxsDefs.view -> Choice bexprs) ->
          do bexprs' <- Set.fromList <$> Monad.mapM (exclamToQst beenHere) (Set.toList bexprs)
             return (choice bexprs')
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do bexprs' <- Monad.mapM (exclamToQst beenHere) bexprs
             return (parallel cidSet bexprs')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do bexpr' <- exclamToQst beenHere bexpr
             return (hide cidSet bexpr')
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do bexpr1' <- exclamToQst beenHere bexpr1
             (acceptOffers', extraConditions) <- doChanOffers acceptOffers
             bexpr2' <- exclamToQst beenHere bexpr2
             return (enable bexpr1' acceptOffers' (guard (ValExpr.cstrAnd (Set.fromList extraConditions)) bexpr2'))
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do bexpr1' <- exclamToQst beenHere bexpr1
             bexpr2' <- exclamToQst beenHere bexpr2
             return (disable bexpr1' bexpr2')
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do bexpr1' <- exclamToQst beenHere bexpr1
             bexpr2' <- exclamToQst beenHere bexpr2
             return (interrupt bexpr1' bexpr2')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do actOffer' <- doActOffer actOffer
             bexpr' <- exclamToQst beenHere bexpr
             return (actionPref actOffer' bexpr')
      (TxsDefs.view -> ValueEnv venv bexpr) ->
          do bexpr' <- exclamToQst beenHere bexpr
             return (valueEnv venv bexpr')
      -- (TxsDefs.view -> StAut _sid _venv transitions) -> 
          -- foldParProcMaps soFar (map actoffer transitions)
      _ -> return (error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!"))
-- exclamToQst

doActOffer :: TxsDefs.ActOffer -> IOC.IOC TxsDefs.ActOffer
doActOffer actOffer = do
    r <- Monad.mapM doOffer (Set.toList (TxsDefs.offers actOffer))
    let newOffers = Set.fromList (map fst r)
    let newConstraint = ValExpr.cstrAnd (Set.fromList (TxsDefs.constraint actOffer : concatMap snd r))
    return (actOffer { TxsDefs.offers = newOffers, TxsDefs.constraint = newConstraint })
-- doActOffer

doOffer :: TxsDefs.Offer -> IOC.IOC (TxsDefs.Offer, [TxsDefs.VExpr])
doOffer offer = do
    (newChanOffers, extraConditions) <- doChanOffers (TxsDefs.chanoffers offer)
    return (offer { TxsDefs.chanoffers = newChanOffers }, extraConditions)
-- doOffer

doChanOffers :: [TxsDefs.ChanOffer] -> IOC.IOC ([TxsDefs.ChanOffer], [TxsDefs.VExpr])
doChanOffers offerList = do
    r <- Monad.mapM doChanOffer offerList
    return (map fst r, concatMap snd r)
-- doChanOffer

doChanOffer :: TxsDefs.ChanOffer -> IOC.IOC (TxsDefs.ChanOffer, [TxsDefs.VExpr])
doChanOffer (TxsDefs.Quest vid) = return (TxsDefs.Quest vid, [])
doChanOffer (TxsDefs.Exclam vexpr) = do
    newVid <- createFreshVar (SortOf.sortOf vexpr)
    return (TxsDefs.Quest newVid, [ValExpr.cstrEqual (ValExpr.cstrVar newVid) vexpr])
-- doChanOffer


