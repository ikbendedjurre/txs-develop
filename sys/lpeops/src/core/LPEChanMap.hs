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
LPEChanSignature,
LPEChanMap,
addToChanMap,
selectChanMapKeys,
getActOfferFromChanMap,
getActOfferDataFromChanMap,
getMultiChannelFromChanMap,
getAllChannelsFromChanMap,
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

type LPEChanSignature = ([ChanId.ChanId], [SortId.SortId])

type LPEChanMap = Map.Map ChanId.ChanId LPEChanSignature

addToChanMap :: LPEChanMap -> BehExprDefs.ActOffer -> IOC.IOC (ChanId.ChanId, LPEChanMap)
addToChanMap chanMap actOffer = do
    let orderedOffers = getOrderedOffers (Set.toList (BehExprDefs.offers actOffer))
    let orderedChans = map BehExprDefs.chanid orderedOffers
    let orderedChanSorts = concatMap getChanOfferSorts orderedOffers
    let orderedHiddenVarSorts = map SortOf.sortOf (Set.toList (BehExprDefs.hiddenvars actOffer))
    let chanSignature = (orderedChans, orderedChanSorts ++ orderedHiddenVarSorts)
    let matches = Map.filter (\v -> v == chanSignature) chanMap
    if matches /= Map.empty
    then return (Map.keys matches !! 0, chanMap)
    else do freshChan <- createFreshChanFromChansAndSorts orderedChans orderedHiddenVarSorts
            return (freshChan, Map.insert freshChan chanSignature chanMap)
  where
    getOrderedOffers :: [BehExprDefs.Offer] -> [BehExprDefs.Offer]
    getOrderedOffers [] = [BehExprDefs.Offer { BehExprDefs.chanid = TxsDefs.chanIdIstep 
                                             , BehExprDefs.chanoffers = []
                                             }]
    getOrderedOffers xs = xs
    -- getOrderedOffers
    
    getChanOfferSorts :: BehExprDefs.Offer -> [SortId.SortId]
    getChanOfferSorts offer = map SortOf.sortOf (BehExprDefs.chanoffers offer)
-- addToChanMap

selectChanMapKeys :: LPEChanMap -> Set.Set ChanId.ChanId -> Set.Set ChanId.ChanId
selectChanMapKeys chanMap requiredChans = Map.keysSet (Map.filter containsRequiredChans chanMap)
  where
    containsRequiredChans :: LPEChanSignature -> Bool
    containsRequiredChans (chans, _) = Set.intersection (Set.fromList chans) requiredChans /= Set.empty
-- selectChanMapKeys

getActOfferFromChanMap :: LPEChanMap -> ChanId.ChanId -> [VarId.VarId] -> TxsDefs.VExpr -> BehExprDefs.ActOffer
getActOfferFromChanMap chanMap chanId chanVars guard =
    case chanMap Map.!? chanId of
      Just (originalChanIds, _) -> iter emptyActOffer originalChanIds chanVars
      Nothing -> error ("Unknown channel found during conversion from restricted LPE form to regular LPE form (" ++ show chanId ++ ")!") -- Should not happen!
  where
    emptyActOffer :: BehExprDefs.ActOffer
    emptyActOffer = BehExprDefs.ActOffer {
                        BehExprDefs.offers = Set.empty
                      , BehExprDefs.hiddenvars = Set.empty
                      , BehExprDefs.constraint = guard
                    }
    -- emptyActOffer
    
    iter :: BehExprDefs.ActOffer -> [ChanId.ChanId] -> [VarId.VarId] -> BehExprDefs.ActOffer
    iter soFar [] remainingVars = soFar { BehExprDefs.hiddenvars = Set.fromList remainingVars }
    iter soFar (cid:remainingChans) remainingVars =
        let varCount = length (ChanId.chansorts cid) in
          if length remainingVars < varCount
          then error "Insufficient communication variables to convert from restricted LPE form to regular LPE form!" -- Should not happen!
          else let (prefix, suffix) = List.splitAt varCount remainingVars in
               let newOffer = BehExprDefs.Offer {
                                  BehExprDefs.chanid = cid
                                , BehExprDefs.chanoffers = map BehExprDefs.Quest prefix
                              } in
               let newOffers = Set.insert newOffer (BehExprDefs.offers soFar) in
                 iter (soFar { BehExprDefs.offers = newOffers }) remainingChans suffix
-- getActOfferFromChanMap

getActOfferDataFromChanMap :: LPEChanMap -> ChanId.ChanId -> [VarId.VarId] -> ([(ChanId.ChanId, [VarId.VarId])], [VarId.VarId])
getActOfferDataFromChanMap chanMap chanId chanVars =
    case chanMap Map.!? chanId of
      Just (originalChanIds, _) -> iter originalChanIds chanVars
      Nothing -> ([(chanId, chanVars)], [])
  where
    iter :: [ChanId.ChanId] -> [VarId.VarId] -> ([(ChanId.ChanId, [VarId.VarId])], [VarId.VarId])
    iter [] remainingVars = ([], remainingVars)
    iter (cid:remainingChans) remainingVars =
        let varCount = length (ChanId.chansorts cid) in
          if length remainingVars < varCount
          then error "Insufficient communication variables!" -- Should not happen!
          else let (prefix, suffix) = List.splitAt varCount remainingVars in
               let (restVarsPerChan, restHiddenVars) = iter remainingChans suffix in
                 ((cid, prefix):restVarsPerChan, restHiddenVars)
-- getActOfferDataFromChanMap

-- Note that this function uses the input parameter as fallback!
getMultiChannelFromChanMap :: LPEChanMap -> ChanId.ChanId -> Set.Set ChanId.ChanId
getMultiChannelFromChanMap chanMap chanId =
    case chanMap Map.!? chanId of
      Just (originalChanIds, _) -> Set.fromList originalChanIds
      Nothing -> Set.singleton chanId
-- getMultiChannelFromChanMap

-- Note that this function uses the input parameter as fallback!
getAllChannelsFromChanMap :: LPEChanMap -> Set.Set ChanId.ChanId -> Set.Set ChanId.ChanId
getAllChannelsFromChanMap chanMap chanIds = Set.unions (map (getMultiChannelFromChanMap chanMap) (Set.toList chanIds))

-- Note that this function uses the object ids of the input parameter as fallback!
getObjectIdsFromChanMap :: LPEChanMap -> ChanId.ChanId -> Set.Set TxsDefs.Ident
getObjectIdsFromChanMap chanMap chanId =
    case chanMap Map.!? chanId of
      Just (originalChanIds, originalSortIds) -> Set.fromList ((map TxsDefs.IdChan originalChanIds) ++ (map TxsDefs.IdSort originalSortIds))
      Nothing -> Set.fromList (TxsDefs.IdChan chanId : map TxsDefs.IdSort (ChanId.chansorts chanId))
-- getObjectIdsFromChanMap


