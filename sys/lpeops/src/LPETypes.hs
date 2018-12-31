{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPETypes
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module LPETypes (
toLPEModel,
fromLPEModel,
getProcessProblems,
module LPETypeDefs
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
import qualified CstrId
import qualified FuncId
import qualified SortId
import qualified VarId
import qualified ChanId
import           Constant hiding (args, sort)
import           ValExpr
import           LPEPrettyPrint
import           LPETypeDefs
import           ValExprVisitor
import           ConcatEither

-- Constructs an LPEModel from a process expression (unless there is a problem).
-- The process expression should be the instantiation of a process that is already linear.
toLPEModel :: TxsDefs.ModelDef                       -- Process instantiation.
           -> IOC.IOC (Either [String] LPEModel)     -- Instance (unless there are problems).
toLPEModel modelDef@(TxsDefs.ModelDef _ _ _ procInst) = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } -> let procDefs = TxsDefs.procDefs tdefs in
        case TxsDefs.view procInst of
          TxsDefs.ProcInst procId _chans paramValues -> case Map.lookup procId procDefs of
            Just procDef@(TxsDefs.ProcDef chans params body) ->
              let (paramEqs, paramEqsProblems) = getParamEqs "model initiation" params paramValues in
                case getLPESummands procId procDef body of
                  Left msgs -> return (Left msgs)
                  Right summands -> do let result = (ProcId.name procId, chans, paramEqs, Set.fromList summands)
                                       let problems = paramEqsProblems ++ getProcessProblems result
                                       if null problems
                                       then return (Right (tdefs, modelDef, result))
                                       else return (Left problems)
            Nothing -> do let definedProcessNames = List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys procDefs))
                          return (Left ["Expected " ++ definedProcessNames ++ ", found " ++ show (Text.unpack (ProcId.name procId)) ++ "!"])
          _ -> return (Left ["Expression must be process instantiation, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"])
      _ -> return (Left ["TorXakis core is not initialized!"])
-- toLPEModel

-- Helper function.
-- Constructs one or more summands from a TXS process expression (unless there are problems):
getLPESummands :: TxsDefs.ProcId -> TxsDefs.ProcDef -> TxsDefs.BExpr -> Either [String] [LPESummand]
getLPESummands expectedProcId expectedProcDef@(TxsDefs.ProcDef defChanIds params _body) expr =
    case TxsDefs.view expr of
      TxsDefs.Choice choices -> concatEither (map (getLPESummands expectedProcId expectedProcDef) (Set.toList choices))
      TxsDefs.ActionPref TxsDefs.ActOffer { TxsDefs.offers = offers, TxsDefs.hiddenvars = hiddenvars, TxsDefs.constraint = constraint } procInst ->
          case TxsDefs.view procInst of
            TxsDefs.ProcInst procId chanIds paramValues
                | procId /= expectedProcId -> Left ["Instantiating different process, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
                | chanIds /= defChanIds -> Left ["Channel mismatch in recursion, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
                | otherwise ->
                    let (paramEqs, paramEqsProblems) = getParamEqs "process instantiation" params paramValues in
                      case concatEither (map (getChannelOffer params) (Set.toList offers)) of
                        Left msgs -> Left (("Recursion " ++ TxsShow.fshow procInst ++ " is invalid because"):msgs)
                        Right channelOffers -> let channelVars = concatMap snd channelOffers ++ Set.toList hiddenvars in
                                               let constructedSummand = LPESummand channelVars channelOffers constraint paramEqs in
                                               let problems = paramEqsProblems ++ getSummandProblems "summand" (Set.fromList params) constructedSummand in
                                                 if null problems
                                                 then Right [constructedSummand]
                                                 else Left (("Summand " ++ showLPESummand constructedSummand ++ " is invalid because"):problems)
            _ -> Left ["Expected recursion, found " ++ TxsShow.fshow (TxsDefs.view procInst) ++ "!"]
      _ -> Left ["Expected choice or channel, found " ++ TxsShow.fshow (TxsDefs.view expr) ++ "!"]
-- getLPESummands

-- Helper method.
-- Extracts LPEParamEqs from given lists, as well as any problems therein:
getParamEqs :: String -> [VarId.VarId] -> [TxsDefs.VExpr] -> (LPEParamEqs, [String])
getParamEqs location params paramValues =
    let paramEqs = Map.fromList (zip params paramValues) in
    let problems = getSortsProblems location (map SortOf.sortOf params) (map SortOf.sortOf paramValues) in
      (paramEqs, problems)
-- getParamEqs

-- Helper method.
-- Extracts an LPEChannelOffer for each channel offer (unless there are problems):
getChannelOffer :: [VarId.VarId] -> TxsDefs.Offer -> Either [String] [LPEChannelOffer]
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
fromLPEModel :: LPEModel -> String -> IOC.IOC (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef)
fromLPEModel (_, _, (_, chans, paramEqs, summands)) procName = do
    let orderedParams = Map.keys paramEqs
    newProcUnid <- IOC.newUnid
    let newProcId = TxsDefs.ProcId { ProcId.name = Text.pack procName
                                   , ProcId.unid = newProcUnid
                                   , ProcId.procchans = map (ProcId.ChanSort . ChanId.chansorts) chans
                                   , ProcId.procvars = map VarId.varsort orderedParams
                                   , ProcId.procexit = ProcId.NoExit }
    let newProcInit = TxsDefs.procInst newProcId chans (paramEqsLookup orderedParams paramEqs)
    let newProcBody = TxsDefs.choice (Set.fromList (map (summandToBExpr newProcId orderedParams) (Set.toList summands)))
    let newProcDef = TxsDefs.ProcDef chans orderedParams newProcBody
    return (newProcInit, newProcId, newProcDef)
  where
      -- Constructs a process expression from a summand:
      summandToBExpr :: TxsDefs.ProcId -> [VarId.VarId] -> LPESummand -> TxsDefs.BExpr
      summandToBExpr lpeProcId lpeOrderedParams (LPESummand chanVars chanOffers gd eqs) =
          let usedChanVars = concatMap snd chanOffers in
          let hiddenChanVars = Set.fromList chanVars Set.\\ Set.fromList usedChanVars in
          let actPref = TxsDefs.ActOffer { TxsDefs.offers = Set.fromList (map offerToOffer chanOffers), TxsDefs.constraint = gd, TxsDefs.hiddenvars = hiddenChanVars } in
          let procInst = TxsDefs.procInst lpeProcId chans (paramEqsLookup lpeOrderedParams eqs) in
            TxsDefs.actionPref actPref procInst
      -- summandToBExpr
      
      -- Constructs an offer from an offer:
      offerToOffer :: LPEChannelOffer -> TxsDefs.Offer
      offerToOffer (chanId, chanVars) = TxsDefs.Offer { TxsDefs.chanid = chanId, TxsDefs.chanoffers = [TxsDefs.Quest var | var <- chanVars] }
-- fromLPEModel

-- This method can detect certain problems with an LPE, making finding bugs in LPE operations easier:
getProcessProblems :: LPEProcess -> [String]
getProcessProblems (_, _chanIds, initParamEqs, summands) =
    concatMap getSmdProblems (zip [1..] (Set.toList summands))
  where
    getSmdProblems :: (Int, LPESummand) -> [String]
    getSmdProblems (n, smd) = getSummandProblems ("summand " ++ show n) (Map.keysSet initParamEqs) smd
-- getProcessProblems

getSummandProblems :: String -> Set.Set VarId.VarId -> LPESummand -> [String]
getSummandProblems location scope (LPESummand channelVars _channelOffers guard paramEqs) =
    let newScope = Set.union scope (Set.fromList channelVars) in
      getValExprProblems ("guard " ++ location) newScope guard ++ getProcInstProblems newScope
  where
    getProcInstProblems :: Set.Set VarId.VarId -> [String]
    getProcInstProblems scp =
        let nonExistentParameters = Map.keysSet paramEqs Set.\\ scope in
          map (\p -> "Assigned parameter " ++ Text.unpack (VarId.name p) ++ " does not exist in process instantiation!") (Set.toList nonExistentParameters)
          ++
          concatMap (getValExprProblems ("process instantiation of " ++ location) scp . snd) (Map.toList paramEqs)
-- getSummandProblems

getValExprProblems :: String -> Set.Set VarId.VarId -> TxsDefs.VExpr -> [String]
getValExprProblems location scope = customData . visitValExpr getProblemsVisitor
  where
    getProblemsVisitor :: [ValExprVisitorOutput [String]] -> TxsDefs.VExpr -> ValExprVisitorOutput [String]
    getProblemsVisitor subExps expr =
        let problems = case expr of
                        (view -> Vconst (Cbool _))        -> []
                        (view -> Vconst (Cint _))         -> []
                        (view -> Vconst (Cstring _))      -> []
                        (view -> Vconst (Cregex _))       -> []
                        (view -> Vconst (Ccstr cid args)) ->
                            getSortsProblems ("constant \"" ++ Text.unpack (CstrId.name cid) ++ "\" constructor in " ++ location) (CstrId.cstrargs cid) (map SortOf.sortOf args)
                        (view -> Vconst (Cany _))         -> []
                        (view -> Vvar vid)                ->
                            ["Variable \"" ++ Text.unpack (VarId.name vid) ++ "\" is not in scope for " ++ location ++ "!" | Set.notMember vid scope]
                        (view -> Vfunc fid args)          ->
                            getSortsProblems ("function \"" ++ Text.unpack (FuncId.name fid) ++ "\" call in " ++ location) (FuncId.funcargs fid) (map SortOf.sortOf args)
                        (view -> Vcstr cid args)          ->
                            getSortsProblems ("\"" ++ Text.unpack (CstrId.name cid) ++ "\" constructor in " ++ location) (CstrId.cstrargs cid) (map SortOf.sortOf args)
                        (view -> Viscstr cid arg)         ->
                            getSortProblems ("recognizer \"is" ++ Text.unpack (CstrId.name cid) ++ "\" call in " ++ location) (CstrId.cstrsort cid) (SortOf.sortOf arg)
                        (view -> Vaccess cid n _ arg)     ->
                            getSortProblems ("accessor \"" ++ Text.unpack n ++ "\" call in " ++ location) (CstrId.cstrsort cid) (SortOf.sortOf arg)
                        (view -> Vite{})                  -> [] -- TODO
                        (view -> Vdivide _ _)             -> [] -- TODO
                        (view -> Vmodulo _ _)             -> [] -- TODO
                        (view -> Vgez _)                  -> [] -- TODO
                        (view -> Vsum _)                  -> [] -- TODO
                        (view -> Vproduct _)              -> [] -- TODO
                        (view -> Vequal _ _)              -> [] -- TODO
                        (view -> Vand _)                  -> [] -- TODO
                        (view -> Vnot _)                  -> [] -- TODO
                        (view -> Vlength _)               -> [] -- TODO
                        (view -> Vat _ _)                 -> [] -- TODO
                        (view -> Vconcat _)               -> [] -- TODO
                        (view -> Vstrinre _ _)            -> [] -- TODO
                        (view -> Vpredef _ fid args)      ->
                            getSortsProblems ("predefined function \"" ++ Text.unpack (FuncId.name fid) ++ "\" call in " ++ location) (FuncId.funcargs fid) (map SortOf.sortOf args)
                        _                                 ->
                            error ("GetValExprProblems.getProblemsVisitor not defined for " ++ show expr ++ "!")
        in ValExprVisitorOutput expr 1 (concatMap customData subExps ++ problems)
-- getValExprProblems

getSortsProblems :: String -> [SortId.SortId] -> [SortId.SortId] -> [String]
getSortsProblems location = getProblems 1
  where
    getProblems :: Int -> [SortId.SortId] -> [SortId.SortId] -> [String]
    getProblems _ [] [] = []
    getProblems n (_:remainingExpected) [] = ["Expected " ++ show (n + length remainingExpected) ++ " arguments in " ++ location ++ ", found " ++ show (n - 1) ++ "!"]
    getProblems n [] (_:remainingFound) = ["Expected " ++ show (n - 1) ++ " arguments in " ++ location ++ ", found " ++ show (n + length remainingFound) ++ "!"]
    getProblems n (e:remainingExpected) (f:remainingFound) = getSortProblems ("argument " ++ show n ++ " in " ++ location) e f ++ getProblems (n + 1) remainingExpected remainingFound
-- compareSorts

getSortProblems :: String -> SortId.SortId -> SortId.SortId -> [String]
getSortProblems location expected found =
    ["Sort mismatch in " ++ location ++ "; found " ++ Text.unpack (SortId.name found) ++ " but expected " ++ Text.unpack (SortId.name expected) ++ "!" | found /= expected]
-- getSortProblems


