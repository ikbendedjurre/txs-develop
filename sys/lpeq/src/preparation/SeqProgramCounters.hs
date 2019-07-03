{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  SeqProgramCounters
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module SeqProgramCounters (
addSeqProgramCounters
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
import qualified ValExpr
import qualified Subst
import qualified FreeVar
import qualified Constant
import qualified ProcId
import qualified ProcDef
import qualified ChanId
import qualified VarId
import BehExprDefs
import ActOfferFactory
import ProcIdFactory
import VarFactory

import UniqueObjects

import qualified ProcInstUpdates

import ProcDepTree

addSeqProgramCounters :: TxsDefs.BExpr -> IOC.IOC TxsDefs.BExpr
addSeqProgramCounters bexpr = do
    bexpr' <- ensureFreshVarsInBExpr bexpr
    procDepTree <- getProcDepTree bexpr'
    let orderedProcs = getProcsOrderedByMaxDepth procDepTree
    procInstUpdateMap <- Monad.foldM addSeqPCsToProc Map.empty orderedProcs
    return (ProcInstUpdates.applyMapToProcInst procInstUpdateMap bexpr')
-- addSeqProgramCounters

addSeqPCsToProc :: ProcInstUpdates.ProcInstUpdateMap -> ProcId.ProcId -> IOC.IOC ProcInstUpdates.ProcInstUpdateMap
addSeqPCsToProc procInstUpdateMap pid = do
    -- IOC.putInfo [ "addSeqPCsToProc " ++ TxsShow.fshow ProcId.name pid ]
    r <- getProcById pid
    case r of
      Just (ProcDef.ProcDef cidDecls vidDecls body) -> do
          seqPC <- createFreshIntVarFromPrefix "seqPC"
          extraVids <- getExtraVidDecls (Set.singleton pid) body
          let ownerVidDecls = seqPC:Set.toList extraVids
          newProcInstUpdate <- ProcInstUpdates.createWithFreshPid pid vidDecls ownerVidDecls (Map.singleton seqPC (ValExpr.cstrConst (Constant.Cint 0)))
          -- IOC.putMsgs [ EnvData.TXS_CORE_USER_INFO ("update " ++ ProcInstUpdates.showItem newProcInstUpdate) ]
          let procInstUpdateMap' = Map.insert pid newProcInstUpdate procInstUpdateMap
          (_, body', _, _) <- constructBExpr procInstUpdateMap' (fst newProcInstUpdate) cidDecls ownerVidDecls seqPC 0 (body, Set.empty, Map.singleton pid 0, 0)
          
          -- unregisterProc pid -- TODO Do this later
          registerProc (fst newProcInstUpdate) (ProcDef.ProcDef cidDecls ownerVidDecls (choice body'))
          return procInstUpdateMap'
      Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
-- addSeqPCsToProc

getExtraVidDecls :: Set.Set ProcId.ProcId -> TxsDefs.BExpr -> IOC.IOC (Set.Set VarId.VarId)
getExtraVidDecls visitedProcs currentBExpr =
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
             if Set.member pid visitedProcs
             then return (extractFreeVidsFromProcInst currentBExpr)
             else do r <- getProcById pid
                     case r of
                       -- (We ignore the declared parameters; if they are never used, we do not need to set them, anyway.)
                       Just (ProcDef.ProcDef _cidDecls _vidDecls body) -> do
                           extraVids <- getExtraVidDecls (Set.insert pid visitedProcs) body
                           return (Set.union extraVids (extractFreeVidsFromProcInst currentBExpr))
                       Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      (TxsDefs.view -> Guard g bexpr) ->
          do extraVids <- getExtraVidDecls visitedProcs bexpr
             return (Set.union (Set.fromList (FreeVar.freeVars g)) extraVids)
      (TxsDefs.view -> Choice bexprs) ->
          Set.unions <$> Monad.mapM (getExtraVidDecls visitedProcs) (Set.toList bexprs)
      (TxsDefs.view -> Parallel _cidSet bexprs) ->
          return (extractFreeVidsFromProcInsts bexprs)
      (TxsDefs.view -> Hide _cidSet bexpr) ->
          getExtraVidDecls visitedProcs bexpr
      (TxsDefs.view -> Enable bexpr1 _acceptOffers bexpr2) ->
          return (extractFreeVidsFromProcInsts [bexpr1, bexpr2])
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          return (extractFreeVidsFromProcInsts [bexpr1, bexpr2])
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          return (extractFreeVidsFromProcInsts [bexpr1, bexpr2])
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do extraVids <- getExtraVidDecls visitedProcs bexpr
             return (Set.union (Set.fromList (FreeVar.freeVars (TxsDefs.constraint actOffer))) extraVids)
      (TxsDefs.view -> ValueEnv _venv _bexpr) ->
          error ("ValueEnv should have been eliminated by now (\"" ++ show currentBExpr ++ "\")!")
      (TxsDefs.view -> StAut _sid _venv _transitions) ->
          error ("StAut should have been eliminated by now (\"" ++ show currentBExpr ++ "\")!")
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- getExtraVidDecls

extractFreeVidsFromProcInsts :: [TxsDefs.BExpr] -> Set.Set VarId.VarId
extractFreeVidsFromProcInsts bexprs = Set.unions (map extractFreeVidsFromProcInst bexprs)

extractFreeVidsFromProcInst :: TxsDefs.BExpr -> Set.Set VarId.VarId
extractFreeVidsFromProcInst (TxsDefs.view -> ProcInst _ _ vexprs) = Set.fromList (concatMap FreeVar.freeVars vexprs)
extractFreeVidsFromProcInst currentBExpr = error ("Process instantiation expected, but found (\"" ++ TxsShow.fshow currentBExpr ++ "\")!")

type ConstructionState = ( TxsDefs.BExpr                   -- If input: Behavioral expression that must be added to the body of the process that is under construction.
                                                           -- If output: Recursive process instantiation that expresses the input expression.
                         , Set.Set TxsDefs.BExpr           -- Contains the body so far of the process that is under construction.
                         , Map.Map ProcId.ProcId Integer   -- Contains initial value of the PC for visiting a particular process.
                         , Integer )                       -- Next available value for the PC.
-- ConstructionState

constructBExpr :: ProcInstUpdates.ProcInstUpdateMap    -- Contains information about how parallel processes on which we are dependent should be instantiated.
               -> ProcId.ProcId                        -- ID of the process to which we are adding a sequential PC.
               -> [ChanId.ChanId]                      -- All channels of the process to which we are adding a sequential PC (same for all processes!).
               -> [VarId.VarId]                        -- All parameters of the process to which we are adding a sequential PC (including the PC).
               -> VarId.VarId                          -- The sequential PC.
               -> Integer                              -- Value of the PC at the level of the current behavioral expression.
               -> ConstructionState                    -- Input construction state.
               -> IOC.IOC ConstructionState            -- Output construction state.
constructBExpr procInstUpdateMap ownerPid ownerCids ownerVidDecls seqPC seqPCValue (currentBExpr, bodySoFar, visitedProcs, _nextSeqPC) = do
    let defaultConstructBExpr = constructBExpr procInstUpdateMap ownerPid ownerCids ownerVidDecls seqPC
    let getOwnerProcInst pc = let f vid = if vid == seqPC
                                          then ValExpr.cstrConst (Constant.Cint pc)
                                          else ValExpr.cstrVar vid in procInst ownerPid ownerCids (map f ownerVidDecls)
    case currentBExpr of
      (TxsDefs.view -> ProcInst pid _cids vexprs) ->
          do r <- getProcById pid
             case r of
               Just (ProcDef.ProcDef _cidDecls vidDecls body) ->
                   case visitedProcs Map.!? pid of
                     Just initSeqPC -> do
                         let f vid = case List.elemIndex vid vidDecls of
                                       Just i -> vexprs !! i
                                       Nothing -> if vid == seqPC
                                                  then ValExpr.cstrConst (Constant.Cint initSeqPC)
                                                  else ValExpr.cstrVar vid
                         let ownerProcInst = procInst ownerPid ownerCids (map f ownerVidDecls)
                         return (ownerProcInst, bodySoFar, visitedProcs, seqPCValue)
                     Nothing -> do
                         (_, bodySoFar', visitedProcs', nextSeqPC') <- defaultConstructBExpr seqPCValue (body, bodySoFar, Map.insert pid seqPCValue visitedProcs, 0)
                         let f vid = case List.elemIndex vid vidDecls of
                                       Just i -> vexprs !! i
                                       Nothing -> if vid == seqPC
                                                  then ValExpr.cstrConst (Constant.Cint seqPCValue)
                                                  else ValExpr.cstrVar vid
                         let ownerProcInst = procInst ownerPid ownerCids (map f ownerVidDecls)
                         return (ownerProcInst, bodySoFar', visitedProcs', nextSeqPC')
               Nothing -> error ("Unknown process (\"" ++ show pid ++ "\")!")
      (TxsDefs.view -> Guard g bexpr) ->
          do let g' = ValExpr.cstrEqual (ValExpr.cstrVar seqPC) (ValExpr.cstrConst (Constant.Cint seqPCValue))
             (bexpr', bodySoFar', visitedProcs', nextSeqPC') <- defaultConstructBExpr (seqPCValue + 1) (bexpr, bodySoFar, visitedProcs, 0)
             let bexpr'' = guard (ValExpr.cstrAnd (Set.fromList [g, g'])) bexpr'
             return (getOwnerProcInst seqPCValue, Set.insert bexpr'' bodySoFar', visitedProcs', nextSeqPC')
      (TxsDefs.view -> Choice bexprs) ->
             if Set.null bexprs
             then return (getOwnerProcInst (-1), bodySoFar, visitedProcs, seqPCValue)
             else do let f (bsf, vp, _nspc) b = do (_b', bsf', vp', nspc') <- defaultConstructBExpr seqPCValue (b, bsf, vp, 0)
                                                   return (bsf', vp', nspc')
                     (bodySoFar', visitedProcs', nextSeqPC') <- Monad.foldM f (bodySoFar, visitedProcs, 0) (Set.toList bexprs)
                     return (getOwnerProcInst seqPCValue, bodySoFar', visitedProcs', nextSeqPC')
      (TxsDefs.view -> Hide cidSet bexpr) ->
          do let g' = ValExpr.cstrEqual (ValExpr.cstrVar seqPC) (ValExpr.cstrConst (Constant.Cint seqPCValue))
             (bexpr', bodySoFar', visitedProcs', nextSeqPC') <- defaultConstructBExpr (seqPCValue + 1) (bexpr, bodySoFar, visitedProcs, 0)
             let bexpr'' = hide cidSet (guard g' bexpr')
             return (getOwnerProcInst seqPCValue, Set.insert bexpr'' bodySoFar', visitedProcs', nextSeqPC')
      (TxsDefs.view -> ActionPref actOffer bexpr) ->
          do let g' = ValExpr.cstrEqual (ValExpr.cstrVar seqPC) (ValExpr.cstrConst (Constant.Cint seqPCValue))
             (bexpr', bodySoFar', visitedProcs', nextSeqPC') <- defaultConstructBExpr (seqPCValue + 1) (bexpr, bodySoFar, visitedProcs, 0)
             let actOffer' = actOffer { TxsDefs.constraint = ValExpr.cstrAnd (Set.fromList [TxsDefs.constraint actOffer, g']) }
             
             -- Communication variables and state variables (=parameters) should not overlap; this messes up later substitutions.
             -- We ignored this until here, where we substitute the original communication variables with fresh ones:
             let (vizVars, hidVars) = getActOfferVars actOffer
             actOfferSubst <- createFreshVars (Set.union vizVars hidVars)
             let bexpr'' = Subst.subst (Map.map ValExpr.cstrVar actOfferSubst) Map.empty bexpr'
             
             -- Use a dedicated function to replace variables in ActOffers (because Subst.subst replaces free variables only):
             let bexpr''' = actionPref (replaceVarsInActOffer actOfferSubst actOffer') bexpr''
             return (getOwnerProcInst seqPCValue, Set.insert bexpr''' bodySoFar', visitedProcs', nextSeqPC')
      
      -- Non-linear branches are only nested in a guard (they are processed more thoroughly later):
      (TxsDefs.view -> Parallel cidSet bexprs) ->
          do let g' = ValExpr.cstrEqual (ValExpr.cstrVar seqPC) (ValExpr.cstrConst (Constant.Cint seqPCValue))
             let bexprs' = rewriteProcInsts procInstUpdateMap bexprs
             let bexpr'' = guard g' (parallel cidSet bexprs')
             return (getOwnerProcInst seqPCValue, Set.insert bexpr'' bodySoFar, visitedProcs, seqPCValue + 1)
      (TxsDefs.view -> Enable bexpr1 acceptOffers bexpr2) ->
          do let g' = ValExpr.cstrEqual (ValExpr.cstrVar seqPC) (ValExpr.cstrConst (Constant.Cint seqPCValue))
             let [bexpr1', bexpr2'] = rewriteProcInsts procInstUpdateMap [bexpr1, bexpr2]
             let bexpr'' = guard g' (enable bexpr1' acceptOffers bexpr2')
             return (getOwnerProcInst seqPCValue, Set.insert bexpr'' bodySoFar, visitedProcs, seqPCValue + 1)
      (TxsDefs.view -> Disable bexpr1 bexpr2) ->
          do let g' = ValExpr.cstrEqual (ValExpr.cstrVar seqPC) (ValExpr.cstrConst (Constant.Cint seqPCValue))
             let [bexpr1', bexpr2'] = rewriteProcInsts procInstUpdateMap [bexpr1, bexpr2]
             let bexpr'' = guard g' (disable bexpr1' bexpr2')
             return (getOwnerProcInst seqPCValue, Set.insert bexpr'' bodySoFar, visitedProcs, seqPCValue + 1)
      (TxsDefs.view -> Interrupt bexpr1 bexpr2) ->
          do let g' = ValExpr.cstrEqual (ValExpr.cstrVar seqPC) (ValExpr.cstrConst (Constant.Cint seqPCValue))
             let [bexpr1', bexpr2'] = rewriteProcInsts procInstUpdateMap [bexpr1, bexpr2]
             let bexpr'' = guard g' (interrupt bexpr1' bexpr2')
             return (getOwnerProcInst seqPCValue, Set.insert bexpr'' bodySoFar, visitedProcs, seqPCValue + 1)
      (TxsDefs.view -> ValueEnv _venv _bexpr) ->
          error ("ValueEnv should have been eliminated by now (\"" ++ show currentBExpr ++ "\")!")
      (TxsDefs.view -> StAut _sid _venv _transitions) ->
          error ("StAut should have been eliminated by now (\"" ++ show currentBExpr ++ "\")!")
      _ -> error ("Behavioral expression not accounted for (\"" ++ show currentBExpr ++ "\")!")
-- constructBExpr

rewriteProcInsts :: ProcInstUpdates.ProcInstUpdateMap -> [TxsDefs.BExpr] -> [TxsDefs.BExpr]
rewriteProcInsts procInstUpdateMap = map (ProcInstUpdates.applyMapToProcInst procInstUpdateMap)

