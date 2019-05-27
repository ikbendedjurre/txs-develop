{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEConversion
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module LPEConversion (
model2lpe,
lpe2model,
module LPETypes
) where

--import qualified Control.Monad as Monad
import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified EnvData
import qualified SortOf
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified VarId
import qualified ValExpr
import qualified ModelId
import qualified ChanId
import           LPEValidity
import           LPETypes
import           ConcatEither
import           BlindSubst
import           ModelIdFactory
import           LPEChanMap
import           VarFactory
import           ChanFactory
import           LPEBlindSubst

-- Constructs an LPEModel from a process expression (unless there are problems).
-- The process expression should be the instantiation of a process that has already been linearized!
model2lpe :: TxsDefs.ModelId -> IOC.IOC (Either [String] LPE)
model2lpe modelId = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    let mdefs = TxsDefs.modelDefs tdefs
    case [ mdef | (mid, mdef) <- Map.toList mdefs, mid == modelId ] of
      (TxsDefs.ModelDef inChans outChans splsyncs procInst:_) ->
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId _ paramValues -> do
            let pdefs = TxsDefs.procDefs tdefs
            case pdefs Map.!? procId of
              Just procDef@(TxsDefs.ProcDef _chans params body) ->
                case getParamEqs tdefs "model initiation" params paramValues of
                  Left msgs -> return (Left msgs)
                  Right initEqs -> case getSummandData tdefs procId procDef body of
                                     Left msgs -> return (Left msgs)
                                     Right summandData -> do let lpe = emptyLPE { lpeContext = tdefs
                                                                                , lpeSplSyncs = splsyncs -- (We do not really know what this is for, we just remember its value!)
                                                                                , lpeName = Text.pack (Text.unpack (ModelId.name modelId) ++ "_" ++ Text.unpack (ProcId.name procId))
                                                                                , lpeInitEqs = initEqs
                                                                                }
                                                             let chanAlphabet = getChanAlphabet inChans outChans
                                                             IOC.putMsgs [ EnvData.TXS_CORE_ANY ("INS = {" ++ concatMap bla inChans ++ "}") ]
                                                             IOC.putMsgs [ EnvData.TXS_CORE_ANY ("OUTS = {" ++ concatMap bla outChans ++ "}") ]
                                                             IOC.putMsgs [ EnvData.TXS_CORE_ANY ("ALPHABET = {" ++ concatMap bla (Set.toList chanAlphabet) ++ "}") ]
                                                             summandData' <- ensureFreshCommVars (filterSummandDataByChanAlphabet chanAlphabet summandData)
                                                             (refinedSummandData, chanMap) <- refineSummandData summandData'
                                                             let lpe' = lpe { lpeChanMap = chanMap
                                                                            , lpeInChans = Map.keysSet (permittedChanMap (lpeChanMap lpe') inChans)
                                                                            , lpeOutChans = Map.keysSet (permittedChanMap (lpeChanMap lpe') outChans)
                                                                            , lpeSummands = Set.fromList (map (constructFromRefinedSummandData chanMap) refinedSummandData)
                                                                            }
                                                             let problems = validateLPEModel lpe'
                                                             if null problems
                                                             then return (Right lpe')
                                                             else return (Left problems)
              Nothing -> do let definedProcessNames = List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys pdefs))
                            return (Left ["Expected " ++ definedProcessNames ++ ", found " ++ show (Text.unpack (ProcId.name procId)) ++ "!"])
          _ -> return (Left ["Expected process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"])
      [] -> return (Left ["Could not find model " ++ show modelId ++ "!"])
  where
    bla :: Set.Set ChanId.ChanId -> String
    bla cids = "[[ " ++ concatMap (\s -> "{" ++ Text.unpack (ChanId.name s) ++ "}") (Set.toList cids) ++ " ]]"
-- toLPEModel

constructFromRefinedSummandData :: LPEChanMap -> (ChanId.ChanId, [VarId.VarId], TxsDefs.VExpr, LPEParamEqs) -> LPESummand
constructFromRefinedSummandData chanMap (cid, vids, guard, paramEqs) =
    LPESummand { lpeSmdChan = cid
               , lpeSmdVars = vids
               , lpeSmdPriority = False
               , lpeSmdQuiescent = False
               , lpeSmdInvisible = List.null (getChanDataFromChanMap chanMap cid)
               , lpeSmdGuard = guard
               , lpeSmdEqs = paramEqs
               , lpeSmdDebug = ""
               }
-- constructFromRefinedSummandData

-- Refines summand data by removing multiple offers.
refineSummandData :: [(TxsDefs.ActOffer, LPEParamEqs)] -> IOC.IOC ([(ChanId.ChanId, [VarId.VarId], TxsDefs.VExpr, LPEParamEqs)], LPEChanMap)
refineSummandData summandData = do
    let hiddenVidsPerChan = getHiddenVidsPerChan Map.empty summandData
    chanMap <- Map.fromList <$> Monad.mapM getChanMapEntry (Map.toList hiddenVidsPerChan)
    refinedSummandData <- Monad.mapM (getRefinedSummandData hiddenVidsPerChan chanMap) summandData
    return (refinedSummandData, chanMap)
  where
    getHiddenVidsPerChan :: Map.Map [ChanId.ChanId] [VarId.VarId] -> [(TxsDefs.ActOffer, LPEParamEqs)] -> Map.Map [ChanId.ChanId] [VarId.VarId]
    getHiddenVidsPerChan soFar [] = soFar
    getHiddenVidsPerChan soFar ((x, _):xs) =
        let cids = Set.toList (getActOfferChans x) in
        let hiddenVids = Set.toList (TxsDefs.hiddenvars x) in
          case soFar Map.!? cids of
            Just vids -> getHiddenVidsPerChan (Map.insert cids (vids ++ hiddenVids) soFar) xs
            Nothing -> getHiddenVidsPerChan (Map.insert cids hiddenVids soFar) xs
    -- getHiddenVidsPerChan
    
    getChanMapEntry :: ([ChanId.ChanId], [VarId.VarId]) -> IOC.IOC (ChanId.ChanId, LPEChanSignature)
    getChanMapEntry (cids, hiddenVids) = do
        let visibleSorts = concatMap ChanId.chansorts cids
        let hiddenSorts = map SortOf.sortOf hiddenVids
        freshChan <- createFreshChanFromChansAndSorts cids (visibleSorts ++ hiddenSorts)
        return (freshChan, (cids, visibleSorts, hiddenSorts))
    -- getChanMapEntry
    
    getRefinedSummandData :: Map.Map [ChanId.ChanId] [VarId.VarId] -> LPEChanMap -> (TxsDefs.ActOffer, LPEParamEqs) -> IOC.IOC (ChanId.ChanId, [VarId.VarId], TxsDefs.VExpr, LPEParamEqs)
    getRefinedSummandData hiddenVidsPerChan chanMap (actOffer, paramEqs) = do
        let cids = Set.toList (getActOfferChans actOffer)
        let allHiddenVids = hiddenVidsPerChan Map.! cids
        newHiddenVids <- Monad.mapM (makeFreshUnlessInSet (TxsDefs.hiddenvars actOffer)) allHiddenVids
        let matches = Map.filter (\(k, _, _) -> k == cids) chanMap
        let freshChanId = Map.keys matches !! 0
        return (freshChanId, getVisibleVars actOffer ++ newHiddenVids, TxsDefs.constraint actOffer, paramEqs)
    -- getRefinedSummandData
    
    getVisibleVars :: TxsDefs.ActOffer -> [VarId.VarId]
    getVisibleVars actOffer =
        let chanOffers = concatMap TxsDefs.chanoffers (Set.toList (TxsDefs.offers actOffer)) in
          concatMap getVisibleVar chanOffers
    -- getVisibleVars
    
    getVisibleVar :: TxsDefs.ChanOffer -> [VarId.VarId]
    getVisibleVar (TxsDefs.Quest vid) = [vid]
    getVisibleVar _ = []
    
    makeFreshUnlessInSet :: Set.Set VarId.VarId -> VarId.VarId -> IOC.IOC VarId.VarId
    makeFreshUnlessInSet varSet vid = do
        if Set.member vid varSet
        then return vid
        else createFreshVarFromVar vid
    -- makeFreshUnlessInSet
-- getChanMapFromSummandData

-- Ensures that all communication variables are fresh.
-- Also removes occurrences of invisible actions (ISTEP).
ensureFreshCommVars :: [(TxsDefs.ActOffer, LPEParamEqs)] -> IOC.IOC [(TxsDefs.ActOffer, LPEParamEqs)]
ensureFreshCommVars summandData = Monad.mapM ensureInSummand summandData
  where
    ensureInSummand :: (TxsDefs.ActOffer, LPEParamEqs) -> IOC.IOC (TxsDefs.ActOffer, LPEParamEqs)
    ensureInSummand (actOffer, paramEqs) = do
        freshHiddenVids <- (Set.fromList . Map.elems) <$> createFreshVars (TxsDefs.hiddenvars actOffer)
        perOffer <- Monad.mapM ensureInOffer (Set.toList (TxsDefs.offers actOffer))
        let (newOffers, freshVidSubst) = (concatMap fst perOffer, Map.fromList (concatMap snd perOffer))
        newConstraint <- doBlindSubst freshVidSubst (TxsDefs.constraint actOffer)
        newParamEqs <- doBlindParamEqsSubst freshVidSubst paramEqs
        return (TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (newOffers)
                                 , TxsDefs.hiddenvars = freshHiddenVids
                                 , TxsDefs.constraint = newConstraint
                                 }, newParamEqs)
    -- ensureInSummand
    
    ensureInOffer :: TxsDefs.Offer -> IOC.IOC ([TxsDefs.Offer], [(VarId.VarId, TxsDefs.VExpr)])
    ensureInOffer offer = do
        if isInvisibleOffer offer 
        then return ([], [])
        else do perChanOffer <- Monad.mapM ensureInChanOffer (TxsDefs.chanoffers offer)
                let (newChanOffers, freshVidSubst) = (concatMap fst perChanOffer, concatMap snd perChanOffer)
                return ([offer { TxsDefs.chanoffers = newChanOffers }], freshVidSubst)
    -- ensureInOffer
    
    ensureInChanOffer :: TxsDefs.ChanOffer -> IOC.IOC ([TxsDefs.ChanOffer], [(VarId.VarId, TxsDefs.VExpr)])
    ensureInChanOffer (TxsDefs.Quest vid) = do
        freshVid <- createFreshVarFromVar vid
        return ([TxsDefs.Quest freshVid], [(vid, ValExpr.cstrVar freshVid)])
    ensureInChanOffer _ = return ([], []) -- Should not happen!
-- ensureFreshCommVars

-- Only keeps data from summand that use a channel that is in the given channel alphabet.
filterSummandDataByChanAlphabet :: Set.Set (Set.Set ChanId.ChanId) -> [(TxsDefs.ActOffer, LPEParamEqs)] -> [(TxsDefs.ActOffer, LPEParamEqs)]
filterSummandDataByChanAlphabet chanAlphabet summandData = filter (\(a, _) -> isActOfferInChanAlphabet chanAlphabet a) summandData

-- Collects all required data per summand from a hierarchical process expression.
getSummandData :: TxsDefs.TxsDefs -> TxsDefs.ProcId -> TxsDefs.ProcDef -> TxsDefs.BExpr -> Either [String] [(TxsDefs.ActOffer, LPEParamEqs)]
getSummandData tdefs expectedProcId expectedProcDef@(TxsDefs.ProcDef defChanIds params _body) expr =
    case TxsDefs.view expr of
      TxsDefs.Choice choices -> concatEitherList (map (getSummandData tdefs expectedProcId expectedProcDef) (Set.toList choices))
      TxsDefs.ActionPref actOffer procInst ->
          case TxsDefs.view procInst of
            TxsDefs.ProcInst procId chanIds paramValues
                | procId /= expectedProcId -> Left ["Expected instantiation of " ++ show expectedProcId ++ ", found instantiation of " ++ show procId ++ "!"]
                | chanIds /= defChanIds -> Left ["Signature mismatch in channels, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
                | otherwise -> case getParamEqs tdefs "process instantiation" params paramValues of
                                 Left msgs -> Left msgs
                                 Right paramEqs -> let msgs = validateActOffer actOffer in
                                                     if null msgs
                                                     then Left msgs
                                                     else Right [(actOffer, paramEqs)]
            _ -> Left ["Expected process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
      _ -> Left ["Expected choice or action prefix, found " ++ TxsShow.fshow (TxsDefs.view expr) ++ "!"]
  where
    validateActOffer :: TxsDefs.ActOffer -> [String]
    validateActOffer actOffer =
        let offers = Set.toList (TxsDefs.offers actOffer) in
          concatMap validateChanOffer (concatMap TxsDefs.chanoffers offers)
    -- validateActOffer
    
    validateChanOffer :: TxsDefs.ChanOffer -> [String]
    validateChanOffer (TxsDefs.Quest _) = []
    validateChanOffer other = ["Expected communication variable, found " ++ show other ++ "!"]
-- getSummandData

-- Constructs an LPEParamEqs from given input.
-- Occurrences of ANY are replaced by default values of the appropriate Sort.
-- Resulting LPEParamEqs as a whole is also type-checked.
getParamEqs :: TxsDefs.TxsDefs -> String -> [VarId.VarId] -> [TxsDefs.VExpr] -> Either [String] LPEParamEqs
getParamEqs tdefs location params paramValues =
    let msgs = validateSortList location (map SortOf.sortOf params) (map SortOf.sortOf paramValues) in
      if null msgs
      then let newParamValues = map (any2defaultValue tdefs) paramValues in
             Right (Map.fromList (zip params newParamValues))
      else Left msgs
-- getParamEqs

-- Constructs a process expression and a process definition from an LPEModel (unless there is a problem).
-- The process expression creates an instance of the process definition.
lpe2model :: LPE -> IOC.IOC TxsDefs.ModelId
lpe2model lpe = do
    let orderedChanParams = Set.toList (revertSimplChanIdsWithChanMap (lpeChanMap lpe) (lpeChanParams lpe))
    let orderedDataParams = Map.keys (lpeInitEqs lpe)
    
    -- Create a new process:
    newProcUnid <- IOC.newUnid
    let newProcId = TxsDefs.ProcId { ProcId.name = Text.pack (Text.unpack (lpeName lpe) ++ "Process")
                                   , ProcId.unid = newProcUnid
                                   , ProcId.procchans = map (ProcId.ChanSort . ChanId.chansorts) orderedChanParams
                                   , ProcId.procvars = map VarId.varsort orderedDataParams
                                   , ProcId.procexit = ProcId.NoExit }
    let newProcInit = TxsDefs.procInst newProcId orderedChanParams (paramEqsLookup orderedDataParams (lpeInitEqs lpe))
    let newProcBody = TxsDefs.choice (Set.fromList (map (summandToBExpr newProcId orderedChanParams orderedDataParams) (Set.toList (lpeSummands lpe))))
    let newProcDef = TxsDefs.ProcDef orderedChanParams orderedDataParams newProcBody
    
    -- Create a new model:
    newModelId <- getModelIdFromName (lpeName lpe)
    let inChans = Set.toList (Set.map (revertSimplChanIdWithChanMap (lpeChanMap lpe)) (lpeInChans lpe))
    let outChans = Set.toList (Set.map (revertSimplChanIdWithChanMap (lpeChanMap lpe)) (lpeOutChans lpe))
    let newModelDef = TxsDefs.ModelDef inChans outChans (lpeSplSyncs lpe) newProcInit
    
    -- Add process and model:
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    IOC.modifyCS (\st -> st { IOC.tdefs = tdefs { TxsDefs.procDefs = Map.insert newProcId newProcDef (TxsDefs.procDefs tdefs)
                                                , TxsDefs.modelDefs = Map.insert newModelId newModelDef (TxsDefs.modelDefs tdefs)
                                                } })
    
    -- Done!
    return newModelId
  where
      -- Constructs a behavioral expression from a summand.
      summandToBExpr :: TxsDefs.ProcId -> [ChanId.ChanId] -> [VarId.VarId] -> LPESummand -> TxsDefs.BExpr
      summandToBExpr lpeProcId orderedChanParams orderedDataParams summand =
          let actOffer = getActOfferFromChanMap (lpeChanMap lpe) (lpeSmdChan summand) (lpeSmdVars summand) (lpeSmdGuard summand) in
          let procInst = TxsDefs.procInst lpeProcId orderedChanParams (paramEqsLookup orderedDataParams (lpeSmdEqs summand)) in
            TxsDefs.actionPref actOffer procInst
-- fromLPEModel

