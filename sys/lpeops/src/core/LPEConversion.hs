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
import qualified SortOf
import qualified TxsDefs
import qualified TxsShow
import qualified ProcId
import qualified VarId
import qualified BehExprDefs
import qualified ChanId
import           LPEValidity
import           LPETypes
import           ConcatEither
import           BlindSubst
import           ModelIdFactory
import           LPEChanMap

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
                                                                                , lpeSplSyncs = splsyncs
                                                                                , lpeName = ProcId.name procId
                                                                                , lpeInitEqs = initEqs
                                                                                }
                                                             let permittedChans = Set.insert Set.empty (Set.union (Set.fromList inChans) (Set.fromList outChans))
                                                             (lpe', msgs) <- Monad.foldM (foldSummandDataIntoLPE permittedChans) (lpe, []) summandData
                                                             let lpe'' = lpe' { lpeInChans = selectChanMapKeys (lpeChanMap lpe') inChans
                                                                              , lpeOutChans = selectChanMapKeys (lpeChanMap lpe') outChans
                                                                              }
                                                             let problems = msgs ++ validateLPEModel lpe''
                                                             if null problems
                                                             then return (Right lpe'')
                                                             else return (Left problems)
              Nothing -> do let definedProcessNames = List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys pdefs))
                            return (Left ["Expected " ++ definedProcessNames ++ ", found " ++ show (Text.unpack (ProcId.name procId)) ++ "!"])
          _ -> return (Left ["Expected process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"])
      [] -> return (Left ["Could not find model " ++ show modelId ++ "!"])
-- toLPEModel

foldSummandDataIntoLPE :: Set.Set (Set.Set ChanId.ChanId) -> (LPE, [String]) -> (TxsDefs.ActOffer, LPEParamEqs) -> IOC.IOC (LPE, [String])
foldSummandDataIntoLPE permittedChans (lpe, earlierMsgs) (actOffer, paramEqs) = do
    if Set.member (Set.map BehExprDefs.chanid (BehExprDefs.offers actOffer)) permittedChans
    then case concatEither (map getSmdVars (Set.toList (TxsDefs.offers actOffer))) of
           Left msgs -> return (lpe, ["Action offer " ++ TxsShow.fshow actOffer ++ " is invalid because"] ++ msgs)
           Right smdVars -> do (smdChan, newChanMap) <- addToChanMap (lpeChanMap lpe) actOffer
                               let lpeSummand = LPESummand { lpeSmdChan = smdChan
                                                           , lpeSmdVars = smdVars ++ Set.toList (TxsDefs.hiddenvars actOffer)
                                                           , lpeSmdGuard = TxsDefs.constraint actOffer
                                                           , lpeSmdEqs = paramEqs
                                                           , lpeSmdDebug = ""
                                                           }
                               return (lpe { lpeChanMap = newChanMap, lpeSummands = Set.insert lpeSummand (lpeSummands lpe) }, earlierMsgs)
    else return (lpe, earlierMsgs)
  where
    getSmdVars :: TxsDefs.Offer -> Either [String] [VarId.VarId]
    getSmdVars TxsDefs.Offer { TxsDefs.chanoffers = chanoffers } =
        concatEither (map offerToVar chanoffers)
      where
        offerToVar :: TxsDefs.ChanOffer -> Either [String] [VarId.VarId]
        offerToVar (TxsDefs.Quest varId) = Right [varId]
        offerToVar chanOffer = Left ["Invalid channel format, found " ++ TxsShow.fshow chanOffer ++ "!"]
-- foldSummandDataIntoLPE

getSummandData :: TxsDefs.TxsDefs -> TxsDefs.ProcId -> TxsDefs.ProcDef -> TxsDefs.BExpr -> Either [String] [(TxsDefs.ActOffer, LPEParamEqs)]
getSummandData tdefs expectedProcId expectedProcDef@(TxsDefs.ProcDef defChanIds params _body) expr =
    case TxsDefs.view expr of
      TxsDefs.Choice choices -> concatEither (map (getSummandData tdefs expectedProcId expectedProcDef) (Set.toList choices))
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
    let orderedChanParams = Set.toList (lpeChanParams lpe)
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
    let inChans = Set.toList (Set.map (getMultiChannelFromChanMap (lpeChanMap lpe)) (lpeInChans lpe))
    let outChans = Set.toList (Set.map (getMultiChannelFromChanMap (lpeChanMap lpe)) (lpeOutChans lpe))
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

