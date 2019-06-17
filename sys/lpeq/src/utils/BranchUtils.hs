{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  BranchUtils
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module BranchUtils (
removeHide,
applyHide,
applyHideToEither,
applyHideToActOffer,
getBranches,
getBranchSegments,
getBranchChans,
hasBranchChans
) where

-- import qualified Data.Map as Map
import qualified Data.Set as Set
-- import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
-- import qualified ProcId
-- import qualified ProcDef
import qualified ChanId
import qualified VarId
-- import qualified Subst
import BehExprDefs
-- import ProcIdFactory
import ActOfferFactory

removeHide :: TxsDefs.BExpr -> (TxsDefs.BExpr, Set.Set ChanId.ChanId)
removeHide (TxsDefs.view -> Hide cidSet bexpr) = (bexpr, cidSet)
removeHide bexpr = (bexpr, Set.empty)

applyHide :: Set.Set ChanId.ChanId -> TxsDefs.BExpr -> TxsDefs.BExpr
applyHide hiddenChanSet (TxsDefs.view -> Hide cidSet bexpr) = applyHide (Set.union hiddenChanSet cidSet) bexpr
applyHide hiddenChanSet bexpr =
    if Set.null hiddenChanSet
    then bexpr
    else hide hiddenChanSet bexpr
-- applyHide

applyHideToEither :: Set.Set ChanId.ChanId -> Either TxsDefs.BExpr TxsDefs.BExpr -> Either TxsDefs.BExpr TxsDefs.BExpr
applyHideToEither hiddenChanSet (Left bexpr) = Left (applyHide hiddenChanSet bexpr)
applyHideToEither hiddenChanSet (Right bexpr) = Right (applyHide hiddenChanSet bexpr)

applyHideToActOffer :: Set.Set ChanId.ChanId -> TxsDefs.ActOffer -> TxsDefs.ActOffer
applyHideToActOffer hiddenChanSet actOffer =
    let (newOffers, newHiddenVars) = foldl getNewOffers (Set.empty, TxsDefs.hiddenvars actOffer) (TxsDefs.offers actOffer) in
      actOffer { TxsDefs.offers = newOffers, TxsDefs.hiddenvars = newHiddenVars }
  where
    getNewOffers :: (Set.Set TxsDefs.Offer, Set.Set VarId.VarId) -> TxsDefs.Offer -> (Set.Set TxsDefs.Offer, Set.Set VarId.VarId)
    getNewOffers (offersSoFar, hiddenVarsSoFar) offer =
        if Set.member (TxsDefs.chanid offer) hiddenChanSet
        then (offersSoFar, Set.union hiddenVarsSoFar (Set.fromList (getOfferVars offer)))
        else (Set.insert offer offersSoFar, hiddenVarsSoFar)
    -- getNewOffers
-- applyHideToActOffer

getBranches :: TxsDefs.BExpr -> Set.Set TxsDefs.BExpr
getBranches (TxsDefs.view -> Choice bexprs) = bexprs
getBranches bexpr = Set.singleton bexpr

getBranchSegments :: TxsDefs.BExpr -> (Set.Set ChanId.ChanId, TxsDefs.ActOffer, TxsDefs.BExpr)
getBranchSegments currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> Hide cidSet bexpr) -> getFromInnerExpr cidSet bexpr
      _ -> getFromInnerExpr Set.empty currentBExpr
  where
    getFromInnerExpr :: Set.Set ChanId.ChanId -> TxsDefs.BExpr -> (Set.Set ChanId.ChanId, TxsDefs.ActOffer, TxsDefs.BExpr)
    getFromInnerExpr cidSet innerExpr =
        case innerExpr of
          (TxsDefs.view -> ActionPref actOffer bexpr) ->
              case bexpr of
                (TxsDefs.view -> ProcInst {}) -> (cidSet, applyHideToActOffer cidSet actOffer, bexpr)
                _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
          _ -> error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")
    -- getFromInnerExpr
-- getBranchChan

hasBranchChans :: Set.Set ChanId.ChanId -> TxsDefs.BExpr -> Bool
hasBranchChans cids bexpr = getBranchChans bexpr == cids

getBranchChans :: TxsDefs.BExpr -> Set.Set ChanId.ChanId
getBranchChans currentBExpr = let (_, actOffer, _) = getBranchSegments currentBExpr in getActOfferChans actOffer



