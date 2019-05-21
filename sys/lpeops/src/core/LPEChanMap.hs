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
isActOfferInChanAlphabet,
LPEChanSignature,
LPEChanMap,
addToChanMap,
permittedChanMap,
getActOfferFromChanMap,
getActOfferDataFromChanMap,
revertSimplChanIdWithChanMap,
revertSimplChanIdsWithChanMap,
getObjectIdsFromChanMap
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ChanId
import qualified VarId
import qualified SortId
import qualified SortOf
import qualified BehExprDefs
import ChanFactory

-- A 'channel signature' is more precisely the signature of a number of an ActOffer, which
-- can consist of multiple Offers (each with its own ChanId and [SortId]) and hidden variables.
-- This data type gives us a canonical way to list ActOffers.
--
-- The first list of this data type defines the ChanIds of all visible channels in an ActOffer.
-- The second list defines the sorts of the communication variables that the ActOffer uses.
-- (There is some overlap in the information provided by the two lists, which is for convenience.)
type LPEChanSignature = ([ChanId.ChanId], [SortId.SortId])

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

isActOfferInChanAlphabet :: Set.Set (Set.Set ChanId.ChanId) -> BehExprDefs.ActOffer -> Bool
isActOfferInChanAlphabet chanAlphabet candidate = isInChanAlphabet chanAlphabet (Set.map BehExprDefs.chanid (BehExprDefs.offers candidate))

-- Restricts the given ChanMap to entries that originate from one of the specified sets of ChanIds.
permittedChanMap :: LPEChanMap -> [Set.Set ChanId.ChanId] -> LPEChanMap
permittedChanMap chanMap permittedChanSets = Map.filter onlyUsesPermittedChanSets chanMap
  where
    onlyUsesPermittedChanSets :: LPEChanSignature -> Bool
    onlyUsesPermittedChanSets (chans, _) = List.elem (Set.fromList chans) (map removeInvisibleChans permittedChanSets)
-- permittedChanMap

-- Adds an ActOffer to a given ChanMap.
addToChanMap :: LPEChanMap -> BehExprDefs.ActOffer -> IOC.IOC (ChanId.ChanId, LPEChanMap)
addToChanMap chanMap actOffer = do
    -- Get a list of all offers:
    let orderedOffers = Set.toList (BehExprDefs.offers actOffer)
    
    -- Distinguish between visible (/=ISTEP) and invisible (==ISTEP) offers:
    let (invisibleOffers, visibleOffers) = List.partition isInvisibleOffer orderedOffers
    
    -- Concatenate the chanIds and sorts of all visible channels:
    let visibleChans = map BehExprDefs.chanid visibleOffers
    let visibleSorts = concatMap getOfferSorts visibleOffers
    
    -- Concatenate the sorts of all invisible channels, and
    -- also add hidden communication variables (since those are also 'invisible'):
    let hiddenVarSorts = map SortOf.sortOf (Set.toList (BehExprDefs.hiddenvars actOffer))
    let invisibleSorts = concatMap getOfferSorts invisibleOffers ++ hiddenVarSorts
    
    -- Compose the channel signature:
    let chanSignature = (visibleChans, visibleSorts ++ invisibleSorts)
    
    -- Check if the channel signature already exists in the given map:
    let matches = Map.filter (\v -> v == chanSignature) chanMap
    if matches /= Map.empty
    then return (Map.keys matches !! 0, chanMap)
    else do freshChan <- createFreshChanFromChansAndSorts visibleChans invisibleSorts
            return (freshChan, Map.insert freshChan chanSignature chanMap)
  where
    -- Obtains the sorts of the communication variables of a specific offer(/channel).
    getOfferSorts :: BehExprDefs.Offer -> [SortId.SortId]
    getOfferSorts offer = map SortOf.sortOf (BehExprDefs.chanoffers offer)
-- addToChanMap

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

-- Gathers data for a new ActOffer from
--  - a given ChanMap;
--  - the ChanId of a simplified ActOffer; and
--  - a list of variables.
getActOfferDataFromChanMap :: LPEChanMap -> ChanId.ChanId -> [VarId.VarId] -> ([(ChanId.ChanId, [VarId.VarId])], [VarId.VarId])
getActOfferDataFromChanMap chanMap chanId chanVars =
    --Defensive programming, should not happen:
    case chanMap Map.!? chanId of
      Just (originalChanIds, _) -> iter originalChanIds chanVars
      Nothing -> ([(chanId, chanVars)], [])
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
revertSimplChanIdWithChanMap chanMap chanId =
    --Defensive programming, should not happen:
    case chanMap Map.!? chanId of
      Just (originalChanIds, _) -> Set.fromList originalChanIds
      Nothing -> error ("Could not find channel in LPEChanMap (chanId = " ++ show chanId ++ ")!")
-- revertSimplChanIdWithChanMap

-- Obtains all ChanIds that were the origin of the ChanIds in the given set.
revertSimplChanIdsWithChanMap :: LPEChanMap -> Set.Set ChanId.ChanId -> Set.Set ChanId.ChanId
revertSimplChanIdsWithChanMap chanMap chanIds = Set.unions (map (revertSimplChanIdWithChanMap chanMap) (Set.toList chanIds))

-- Note that this function uses the object ids of the input parameter as fallback!
getObjectIdsFromChanMap :: LPEChanMap -> ChanId.ChanId -> Set.Set TxsDefs.Ident
getObjectIdsFromChanMap chanMap chanId =
    case chanMap Map.!? chanId of
      Just (originalChanIds, originalSortIds) -> Set.fromList ((map TxsDefs.IdChan originalChanIds) ++ (map TxsDefs.IdSort originalSortIds))
      Nothing -> Set.fromList (TxsDefs.IdChan chanId : map TxsDefs.IdSort (ChanId.chansorts chanId))
-- getObjectIdsFromChanMap

