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
import qualified ChanId
import           LPEPrettyPrint
import           LPEValidity
import           LPETypes
import           ConcatEither
import           BlindSubst
import           ModelIdFactory

-- Constructs an LPEModel from a process expression (unless there are problems).
-- The process expression should be the instantiation of a process that has already been linearized!
model2lpe :: TxsDefs.ModelId -> IOC.IOC (Either [String] LPE)
model2lpe modelId = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    let mdefs = TxsDefs.modelDefs tdefs
    case [ mdef | (mid, mdef) <- Map.toList mdefs, mid == modelId ] of
      (TxsDefs.ModelDef inChans outChans _splsyncs procInst:_) ->
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId _ paramValues -> do
            let pdefs = TxsDefs.procDefs tdefs
            case pdefs Map.!? procId of
              Just procDef@(TxsDefs.ProcDef chans params body) ->
                let (initEqs, initEqsProblems) = getParamEqs tdefs "model initiation" params paramValues in
                  case getLPESummands tdefs procId procDef body of
                    Left msgs -> return (Left msgs)
                    Right summands -> do let lpe = LPE { lpeContext = tdefs
                                                       , lpeInChans = Set.fromList inChans
                                                       , lpeOutChans = Set.fromList outChans
                                                       , lpeName = ProcId.name procId
                                                       , lpeChanParams = Set.fromList chans
                                                       , lpeInitEqs = initEqs
                                                       , lpeSummands = Set.fromList summands
                                                       }
                                         let problems = initEqsProblems ++ validateLPE lpe
                                         if null problems
                                         then return (Right lpe)
                                         else return (Left problems)
              Nothing -> do let definedProcessNames = List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys pdefs))
                            return (Left ["Expected " ++ definedProcessNames ++ ", found " ++ show (Text.unpack (ProcId.name procId)) ++ "!"])
          _ -> return (Left ["Expected process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"])
      [] -> return (Left ["Could not find model " ++ show modelId ++ "!"])
  where
    getParamEqs :: TxsDefs.TxsDefs -> String -> [VarId.VarId] -> [TxsDefs.VExpr] -> (LPEParamEqs, [String])
    getParamEqs tdefs location params paramValues =
        let newParamValues = map (any2defaultValue tdefs) paramValues in
        let paramEqs = Map.fromList (zip params newParamValues) in
        let problems = validateSortList location (map SortOf.sortOf params) (map SortOf.sortOf newParamValues) in
          (paramEqs, problems)
-- toLPEModel

-- Helper function.
-- Constructs one or more summands from a TXS process expression (unless there are problems).
getLPESummands :: TxsDefs.TxsDefs -> TxsDefs.ProcId -> TxsDefs.ProcDef -> TxsDefs.BExpr -> Either [String] [LPESummand]
getLPESummands tdefs expectedProcId expectedProcDef@(TxsDefs.ProcDef defChanIds params _body) expr =
    case TxsDefs.view expr of
      TxsDefs.Choice choices -> concatEither (map (getLPESummands tdefs expectedProcId expectedProcDef) (Set.toList choices))
      TxsDefs.ActionPref TxsDefs.ActOffer { TxsDefs.offers = offers, TxsDefs.hiddenvars = hiddenvars, TxsDefs.constraint = constraint } procInst ->
          case TxsDefs.view procInst of
            TxsDefs.ProcInst procId chanIds paramValues
                | procId /= expectedProcId -> Left ["Expected instantiation of " ++ show expectedProcId ++ ", found instantiation of " ++ show procId ++ "!"]
                | chanIds /= defChanIds -> Left ["Signature mismatch in channels, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
                | otherwise ->
                    let (paramEqs, paramEqsProblems) = getParamEqs "process instantiation" paramValues in
                      case concatEither (map (getChannelOffer params) (Set.toList offers)) of
                        Left msgs -> Left (("Process instantiation " ++ TxsShow.fshow procInst ++ " is invalid because"):msgs)
                        Right channelOffers -> let channelVars = concatMap snd channelOffers ++ Set.toList hiddenvars in
                                               let lpeSummand = LPESummand { lpeSmdVars = Set.fromList channelVars
                                                                           , lpeSmdOffers = Map.fromList channelOffers
                                                                           , lpeSmdGuard = constraint
                                                                           , lpeSmdEqs = paramEqs
                                                                           } in
                                               let problems = paramEqsProblems ++ validateLPESummand "summand" (Set.fromList params) lpeSummand in
                                                 if null problems
                                                 then Right [lpeSummand]
                                                 else Left (("Summand " ++ showLPESummand lpeSummand ++ " is invalid because"):problems)
            _ -> Left ["Expected process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
      _ -> Left ["Expected choice or action prefix, found " ++ TxsShow.fshow (TxsDefs.view expr) ++ "!"]
  where
    getParamEqs :: String -> [TxsDefs.VExpr] -> (LPEParamEqs, [String])
    getParamEqs location paramValues =
        let newParamValues = map (any2defaultValue tdefs) paramValues in
        let paramEqs = Map.fromList (zip params newParamValues) in
        let problems = validateSortList location (map SortOf.sortOf params) (map SortOf.sortOf paramValues) in
          (paramEqs, problems)
-- getLPESummands

-- Helper method.
-- Extracts an LPEChannelOffer for each channel offer (unless there are problems).
getChannelOffer :: [VarId.VarId] -> TxsDefs.Offer -> Either [String] [LPEChanOffer]
getChannelOffer params TxsDefs.Offer { TxsDefs.chanid = chanid, TxsDefs.chanoffers = chanoffers } =
    case concatEither (map offerToVar chanoffers) of
      Left msgs -> Left msgs
      Right offerVars -> Right [(chanid, offerVars)]
  where
    offerToVar :: TxsDefs.ChanOffer -> Either [String] [VarId.VarId]
    offerToVar (TxsDefs.Quest varId) =
        if varId `elem` params -- The channel variable should be fresh!
        then Left ["Channel variable should be fresh, found " ++ TxsShow.fshow varId ++ "!" ]
        else Right [varId]
    offerToVar chanOffer = Left ["Invalid channel format, found " ++ TxsShow.fshow chanOffer ++ "!"]
-- getChannelOffers

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
    let newModelDef = TxsDefs.ModelDef (Set.toList (lpeInChans lpe)) (Set.toList (lpeOutChans lpe)) [] newProcInit
    
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
          let usedChanVars = Set.fromList (concat (Map.elems (lpeSmdOffers summand))) in
          let actPref = TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (map offerToOffer (Map.toList (lpeSmdOffers summand))),
                                           TxsDefs.constraint = lpeSmdGuard summand,
                                           TxsDefs.hiddenvars = lpeSmdVars summand Set.\\ usedChanVars } in
          let procInst = TxsDefs.procInst lpeProcId orderedChanParams (paramEqsLookup orderedDataParams (lpeSmdEqs summand)) in
            TxsDefs.actionPref actPref procInst
      -- summandToBExpr
      
      -- Constructs an offer from an offer.
      offerToOffer :: LPEChanOffer -> TxsDefs.Offer
      offerToOffer (chanId, chanVars) = TxsDefs.Offer { TxsDefs.chanid = chanId
                                                      , TxsDefs.chanoffers = [TxsDefs.Quest var | var <- chanVars]
                                                      }
-- fromLPEModel

