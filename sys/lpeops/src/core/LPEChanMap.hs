{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEChanMap
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEChanMap (
isInvisibleChan,
isInvisibleOffer,
getChanAlphabet,
isInChanAlphabet,
getActOfferChans,
isActOfferInChanAlphabet,
LPEChanSignature,
LPEChanMap,
permittedChanMap,
getChanDataFromChanMap,
getActOfferFromChanMap,
getActOfferDataFromChanMap,
revertSimplChanIdWithChanMap,
revertSimplChanIdsWithChanMap,
getObjectIdsFromChanMap
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import qualified ChanId
import qualified VarId
import qualified SortId
import qualified BehExprDefs

-- The ActOffer of an LPE summand can consist of multiple Offers (each with its own ChanId and [SortId]) and hidden variables.
-- This is inconvenient for comparing LPE summands, and so we replace them by a fresh ChanId that is always used with the same [SortId] signature.
-- TODO

-- A 'channel signature' is more precisely the signature of a number of an ActOffer, which
-- can consist of multiple Offers (each with its own ChanId and [SortId]) and hidden variables.
-- This data type gives us a canonical way to list ActOffers.
--
-- The first list of this data type defines the ChanIds of all visible channels in an ActOffer.
-- The second list defines the sorts of the communication variables that the ActOffer uses.
-- (There is some overlap in the information provided by the two lists, which is for convenience.)
type LPEChanSignature = ([ChanId.ChanId], [SortId.SortId], [SortId.SortId])

-- ActOffers are frequently replaced by a simplified ActOffer in which multiple Offers are expressed by one Offer which a fresh ChanId.
-- A 'channel map' makes it possible to trace such fresh ChanIds back to their ActOffer of origin.
type LPEChanMap = Map.Map ChanId.ChanId LPEChanSignature

-- Checks if a ChanId is invisible (==ISTEP).
isInvisibleChan :: ChanId.ChanId -> Bool
isInvisibleChan cid = cid == TxsDefs.chanIdIstep

-- Checks if an Offer is invisible (==ISTEP).
isInvisibleOffer :: BehExprDefs.Offer -> Bool
isInvisibleOffer = isInvisibleChan . BehExprDefs.chanid

removeInvisibleChans :: Set.Set ChanId.ChanId -> Set.Set ChanId.ChanId
removeInvisibleChans = Set.filter (not . isInvisibleChan)

getChanAlphabet :: [Set.Set ChanId.ChanId] -> [Set.Set ChanId.ChanId] -> Set.Set (Set.Set ChanId.ChanId)
getChanAlphabet inChans outChans = Set.fromList (map removeInvisibleChans ([Set.empty] ++ inChans ++ outChans))

isInChanAlphabet :: Set.Set (Set.Set ChanId.ChanId) -> Set.Set ChanId.ChanId -> Bool
isInChanAlphabet chanAlphabet candidateChans = Set.member (removeInvisibleChans candidateChans) chanAlphabet

getActOfferChans :: BehExprDefs.ActOffer -> Set.Set ChanId.ChanId
getActOfferChans actOffer = removeInvisibleChans (Set.map BehExprDefs.chanid (BehExprDefs.offers actOffer))

isActOfferInChanAlphabet :: Set.Set (Set.Set ChanId.ChanId) -> BehExprDefs.ActOffer -> Bool
isActOfferInChanAlphabet chanAlphabet candidate = isInChanAlphabet chanAlphabet (getActOfferChans candidate)

-- Restricts the given ChanMap to entries that originate from one of the specified sets of ChanIds.
permittedChanMap :: LPEChanMap -> [Set.Set ChanId.ChanId] -> LPEChanMap
permittedChanMap chanMap permittedChanSets = Map.filter onlyUsesPermittedChanSets chanMap
  where
    onlyUsesPermittedChanSets :: LPEChanSignature -> Bool
    onlyUsesPermittedChanSets (chans, _, _) = List.elem (Set.fromList chans) (map removeInvisibleChans permittedChanSets)
-- permittedChanMap

-- Constructs (often 'reconstructs') a new ActOffer from
--  - a given ChanMap;
--  - the ChanId of a simplified ActOffer;
--  - a list of variables; and
--  - a guard (= boolean expression).
getActOfferFromChanMap :: LPEChanMap -> ChanId.ChanId -> [VarId.VarId] -> TxsDefs.VExpr -> BehExprDefs.ActOffer
getActOfferFromChanMap chanMap chanId chanVars guard =
    let (varsPerChan, hiddenVars) = getActOfferDataFromChanMap chanMap chanId chanVars in
      BehExprDefs.ActOffer { BehExprDefs.offers = Set.fromList (map varsPerChanToOffer varsPerChan)
                           , BehExprDefs.hiddenvars = Set.fromList hiddenVars
                           , BehExprDefs.constraint = guard
                           }
  where
    varsPerChanToOffer :: (ChanId.ChanId, [VarId.VarId]) -> BehExprDefs.Offer
    varsPerChanToOffer (cid, vids) =
        BehExprDefs.Offer { BehExprDefs.chanid = cid
                          , BehExprDefs.chanoffers = map BehExprDefs.Quest vids
                          }
    -- varsPerChanToOffer
-- getActOfferFromChanMap

getChanDataFromChanMap :: LPEChanMap -> ChanId.ChanId -> [ChanId.ChanId]
getChanDataFromChanMap chanMap chanId =
    --Defensive programming:
    case chanMap Map.!? chanId of
      Just (origChanIds, _, _) -> origChanIds
      Nothing -> error ("Could not find channel in LPEChanMap (chanId = " ++ show chanId ++ ")!")
-- getChanDataFromChanMap

-- Gathers data for a new ActOffer from
--  - a given ChanMap;
--  - the ChanId of a simplified ActOffer; and
--  - a list of variables.
getActOfferDataFromChanMap :: LPEChanMap -> ChanId.ChanId -> [VarId.VarId] -> ([(ChanId.ChanId, [VarId.VarId])], [VarId.VarId])
getActOfferDataFromChanMap chanMap chanId chanVars = iter (getChanDataFromChanMap chanMap chanId) chanVars
  where
    iter :: [ChanId.ChanId] -> [VarId.VarId] -> ([(ChanId.ChanId, [VarId.VarId])], [VarId.VarId])
    iter [] remainingVars = ([], remainingVars)
    iter (cid:remainingChans) remainingVars =
        let varCount = length (ChanId.chansorts cid) in
          if length remainingVars < varCount
          then error ("Insufficient communication variables (chanId = " ++ show chanId ++ ", chanVars = " ++ show (chanVars) ++ ")!") -- Should not happen!
          else let (prefix, suffix) = List.splitAt varCount remainingVars in
               let (restVarsPerChan, restHiddenVars) = iter remainingChans suffix in
                 ((cid, prefix):restVarsPerChan, restHiddenVars)
-- getActOfferDataFromChanMap

-- Converts the ChanId of a simplified ActOffer back to the ChanIds of origin.
revertSimplChanIdWithChanMap :: LPEChanMap -> ChanId.ChanId -> Set.Set ChanId.ChanId
revertSimplChanIdWithChanMap chanMap chanId = Set.fromList (getChanDataFromChanMap chanMap chanId)

-- Obtains all ChanIds that were the origin of the ChanIds in the given set.
revertSimplChanIdsWithChanMap :: LPEChanMap -> Set.Set ChanId.ChanId -> Set.Set ChanId.ChanId
revertSimplChanIdsWithChanMap chanMap chanIds = Set.unions (map (revertSimplChanIdWithChanMap chanMap) (Set.toList chanIds))

-- Note that this function uses the object ids of the input parameter as fallback!
getObjectIdsFromChanMap :: LPEChanMap -> ChanId.ChanId -> Set.Set TxsDefs.Ident
getObjectIdsFromChanMap chanMap chanId =
    case chanMap Map.!? chanId of
      Just (origChanIds, origVizSortIds, origHidSortIds) -> Set.fromList ((map TxsDefs.IdChan origChanIds) ++ (map TxsDefs.IdSort origVizSortIds) ++ (map TxsDefs.IdSort origHidSortIds))
      Nothing -> Set.fromList (TxsDefs.IdChan chanId : map TxsDefs.IdSort (ChanId.chansorts chanId))
-- getObjectIdsFromChanMap

