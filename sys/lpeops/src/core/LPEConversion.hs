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
                                                             (lpe', msgs) <- Monad.foldM (foldSummandDataIntoLPE chanAlphabet) (lpe, []) summandData
                                                             let lpe'' = lpe' { lpeInChans = Map.keysSet (permittedChanMap (lpeChanMap lpe') inChans)
                                                                              , lpeOutChans = Map.keysSet (permittedChanMap (lpeChanMap lpe') outChans)
                                                                              }
                                                             let problems = msgs ++ validateLPEModel lpe''
                                                             if null problems
                                                             then return (Right lpe'')
                                                             else return (Left problems)
              Nothing -> do let definedProcessNames = List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys pdefs))
                            return (Left ["Expected " ++ definedProcessNames ++ ", found " ++ show (Text.unpack (ProcId.name procId)) ++ "!"])
          _ -> return (Left ["Expected process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"])
      [] -> return (Left ["Could not find model " ++ show modelId ++ "!"])
  where
    bla :: Set.Set ChanId.ChanId -> String
    bla cids = "[[ " ++ concatMap (\s -> "{" ++ Text.unpack (ChanId.name s) ++ "}") (Set.toList cids) ++ " ]]"
-- toLPEModel

foldSummandDataIntoLPE :: Set.Set (Set.Set ChanId.ChanId) -> (LPE, [String]) -> (TxsDefs.ActOffer, LPEParamEqs) -> IOC.IOC (LPE, [String])
foldSummandDataIntoLPE chanAlphabet (lpe, earlierMsgs) (actOffer, paramEqs) = do
    -- Ignore summands with a channel that is not in the channel alphabet:
    if isActOfferInChanAlphabet chanAlphabet actOffer
    then case concatEitherList (map getSmdVars (Set.toList (TxsDefs.offers actOffer))) of
           Left msgs -> return (lpe, ["Action offer " ++ TxsShow.fshow actOffer ++ " is invalid because"] ++ msgs)
           Right smdVars -> do -- If the chanmap already contains the channel signature, obtain the corresponding (fresh) channel.
                               -- If the chanmap does not yet contain the channel signature, add it and create a fresh channel:
                               (smdChan, newChanMap) <- addToChanMap (lpeChanMap lpe) actOffer
                               -- Guarantee that all local variables of the summand are fresh:
                               let vids = smdVars ++ Set.toList (TxsDefs.hiddenvars actOffer)
                               freshVars <- createFreshVars (Set.fromList vids)
                               let freshVarSubst = Map.map ValExpr.cstrVar freshVars
                               freshVarGuard <- doBlindSubst freshVarSubst (TxsDefs.constraint actOffer)
                               freshVarParamEqs <- doBlindParamEqsSubst freshVarSubst paramEqs
                               -- Combine into summand data:
                               let lpeSummand = LPESummand { lpeSmdChan = smdChan
                                                           , lpeSmdVars = map (\v -> freshVars Map.! v) vids
                                                           , lpeSmdPriority = False
                                                           , lpeSmdQuiescent = False
                                                           , lpeSmdInvisible = False
                                                           , lpeSmdGuard = freshVarGuard
                                                           , lpeSmdEqs = freshVarParamEqs
                                                           , lpeSmdDebug = ""
                                                           }
                               -- Add into LPE that is being folded:
                               return (lpe { lpeChanMap = newChanMap, lpeSummands = Set.insert lpeSummand (lpeSummands lpe) }, earlierMsgs)
    else do IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Deleted non-SYNCS channel (" ++ TxsShow.fshow actOffer ++ ")!") ]
            return (lpe, earlierMsgs)
  where
    getSmdVars :: TxsDefs.Offer -> Either [String] [VarId.VarId]
    getSmdVars TxsDefs.Offer { TxsDefs.chanoffers = chanoffers } =
        concatEitherList (map offerToVar chanoffers)
      where
        offerToVar :: TxsDefs.ChanOffer -> Either [String] [VarId.VarId]
        offerToVar (TxsDefs.Quest varId) = Right [varId]
        offerToVar chanOffer = Left ["Invalid channel format, found " ++ TxsShow.fshow chanOffer ++ "!"]
-- foldSummandDataIntoLPE

-- Collects all required data for each summand from n hierarchical process expression.
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
                                 Right paramEqs -> Right [(actOffer, paramEqs)]
            _ -> Left ["Expected process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
      _ -> Left ["Expected choice or action prefix, found " ++ TxsShow.fshow (TxsDefs.view expr) ++ "!"]
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

