{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEStepper
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns        #-}
module LPEStepper (
stepLPE
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified Data.Map as Map
import qualified Data.Set as Set
-- import qualified EnvBTree as IOB
import qualified EnvCore as IOC
import qualified EnvData
import qualified Satisfiability as Sat
import qualified SolveDefs
import qualified ValExpr
import qualified Constant
-- import qualified Eval
-- import qualified Sigs
-- import qualified TxsDefs
import LPETypes
-- import ConcatEither
import Pairs
import LPEBlindSubst

import qualified Data.List as List
import qualified Data.Text as Text
import qualified ChanId
import qualified VarId
import LPEPrettyPrint
import LPEChanMap

type LPEState = LPEParamEqs
type LPEStates = Set.Set LPEState

-- Removes superfluous summands, e.g. summands that do not add new behavior to the LPE.
stepLPE :: Int -> LPEOperation
stepLPE n lpe _out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("<<step " ++ show n ++ ">>") ]
    doLPESteps lpe (Set.singleton (lpeInitEqs lpe)) n 1
    return (Right lpe)
-- stepLPE

doLPESteps :: LPE -> LPEStates -> Int -> Int -> IOC.IOC ()
doLPESteps lpe states n stepNr = do
    if n == 0
    then IOC.putMsgs [ EnvData.TXS_CORE_ANY ("PASS") ]
    else do maybeNextStates <- getRandomNextStates lpe states
            case maybeNextStates of
              -- Just (_x, _y, nextStates) -> doLPESteps lpe nextStates (n - 1)
              Just (stepSmd, stepSol, nextStates) -> do let (varsPerChan, hiddenVars) = getActOfferDataFromChanMap (lpeChanMap lpe) (lpeSmdChan stepSmd) (lpeSmdVars stepSmd)
                                                        IOC.putMsgs [ EnvData.TXS_CORE_ANY ("STEP " ++ show stepNr ++ ": " ++ showChans stepSol varsPerChan ++ showHiddenVars stepSol hiddenVars ++ " [" ++ show (Set.size states) ++ " -> " ++ show (Set.size nextStates) ++ "]") ]
                                                        doLPESteps lpe nextStates (n - 1) (stepNr + 1)
              Nothing -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("DEADLOCK") ]
  where
    showChans :: LPEParamEqs -> [(ChanId.ChanId, [VarId.VarId])] -> String
    showChans _ [] = "ISTEP"
    showChans sol vidsPerCid = List.intercalate " | " (map (showChan sol) vidsPerCid)
    
    showChan :: LPEParamEqs -> (ChanId.ChanId, [VarId.VarId]) -> String
    showChan sol (cid, vids) = Text.unpack (ChanId.name cid) ++ concatMap (\vid -> " ! " ++ showValExpr (sol Map.! vid)) vids
    
    showHiddenVars :: LPEParamEqs -> [VarId.VarId] -> String
    showHiddenVars _ [] = ""
    showHiddenVars sol vids = " ( " ++ concatMap (\vid -> " ! " ++ showValExpr (sol Map.! vid)) vids ++ " )"
-- doLPESteps

getRandomNextStates :: LPE -> LPEStates -> IOC.IOC (Maybe (LPESummand, LPEParamEqs, LPEStates))
getRandomNextStates lpe currentStates = do
    --if currentStates == Set.empty
    --then IOC.putMsgs [ EnvData.TXS_CORE_ANY ("No states") ]
    --else IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Some state = " ++ showLPEParamEqs ((Set.toList currentStates) !! 0)) ]
    --IOC.putMsgs [ EnvData.TXS_CORE_ANY ("->") ]
    
    shuffledStates <- MonadState.liftIO $ knuthShuffle (Set.toList currentStates)
    shuffledSmds <- MonadState.liftIO $ knuthShuffle (Set.toList (lpeSummands lpe))
    maybeSES <- getSummandEnablingState shuffledStates shuffledSmds
    case maybeSES of
      Just (_state, smd, sol) -> do nextStates <- getStatesAfterSummand smd (Set.toList currentStates) sol
                                    return (Just (smd, sol, Set.fromList nextStates))
      Nothing -> return Nothing
  where
    getSummandEnablingState :: [LPEState] -> [LPESummand] -> IOC.IOC (Maybe (LPEState, LPESummand, LPEParamEqs))
    getSummandEnablingState [] _ = return Nothing
    getSummandEnablingState (state:states) smds = do
        maybeSmdSol <- getSummandEnabledByState smds state
        case maybeSmdSol of
          Just (smd, sol) -> return (Just (state, smd, sol))
          Nothing -> getSummandEnablingState states smds
    -- getSummandEnablingState
    
    getSummandEnabledByState :: [LPESummand] -> LPEState -> IOC.IOC (Maybe (LPESummand, LPEParamEqs))
    getSummandEnabledByState [] _ = return Nothing
    getSummandEnabledByState (smd:smds) state = do
        guardInCurrentState <- doBlindSubst state (lpeSmdGuard smd)
        sol <- Sat.getRandomSolution guardInCurrentState (ValExpr.cstrConst (Constant.Cbool True)) (lpeSmdVars smd)
        case sol of
          SolveDefs.Solved solMap -> return (Just (smd, solutionToParamEqs solMap))
          _ -> getSummandEnabledByState smds state
    -- getSummandEnabledByState
    
    getStatesAfterSummand :: LPESummand -> [LPEParamEqs] -> LPEParamEqs -> IOC.IOC [LPEParamEqs]
    getStatesAfterSummand _ [] _ = return []
    getStatesAfterSummand solSmd (state:states) sol = do
        nextStates <- Monad.mapM (getStateAfterSummand solSmd (Map.union sol state)) (Set.toList (lpeSummands lpe))
        andSoForth <- getStatesAfterSummand solSmd states sol
        return (concat nextStates ++ andSoForth)
    -- getStatesAfterSummand
    
    getStateAfterSummand :: LPESummand -> LPEParamEqs -> LPESummand -> IOC.IOC [LPEParamEqs]
    -- getStateAfterSummand solSmd solState appliedSmd = do
    getStateAfterSummand _ _ _ = do
        return []
        -- if lpeSmdChan appliedSmd /= lpeSmdChan solSmd
        -- then return []
        -- else do let varSubst = Map.fromList (zip (lpeSmdVars appliedSmd) (map ValExpr.cstrVar (lpeSmdVars solSmd)))
                -- guardAfterVarSubst <- doBlindSubst varSubst (lpeSmdGuard appliedSmd)
                -- guardAfterSolState <- doBlindSubst solState guardAfterVarSubst
                -- someSol <- Sat.getSomeSolution2 guardAfterSolState (ValExpr.cstrConst (Constant.Cbool True)) <vars>
                -- case someSol of
                  -- SolveDefs.Solved someSolMap -> do let someSolEqs = solutionToParamEqs someSolMap
                                                    
                  -- _ -> return []
                  
                -- taut <- Sat.isTautology guardAfterSolState (ValExpr.cstrConst (Constant.Cbool True))
                -- if taut
                -- then do paramEqsAfterVarSubst <- doBlindParamEqsSubst varSubst (lpeSmdEqs appliedSmd)
                        -- paramEqsAfterSolState <- doBlindParamEqsSubst solState paramEqsAfterVarSubst
                        -- evaluated <- evalParamEqs paramEqsAfterSolState
                        -- case evaluated of
                          -- Just eqs -> return [eqs]
                          -- Nothing -> return []
                -- else return []
    -- -- getStateAfterSummand
-- getSummandsAndEnablingCommVars

-- evalParamEqs :: LPEParamEqs -> IOC.IOC (Maybe LPEParamEqs)
-- evalParamEqs eqs = do
    -- let eqsList = Map.toList eqs
    -- newVals <- Monad.mapM simplifyExpr (map snd eqsList)
    -- case concatEither newVals of
      -- Left errors -> do Monad.mapM_ (\m -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Error: " ++ m) ]) errors
                        -- return Nothing
      -- Right vals -> return (Just (Map.fromList (zip (map fst eqsList) vals)))
-- -- evalParamEqs

-- simplifyExpr :: TxsDefs.VExpr -> IOC.IOC (Either String TxsDefs.VExpr)
-- simplifyExpr expr = do
    -- case expr of
      -- (ValExpr.view -> ValExpr.Vconst (Constant.Ccstr _ _)) ->
          -- do envb <- filterEnvCtoEnvB
             -- (simplified, envb') <- MonadState.lift $ MonadState.runStateT (Eval.eval expr) envb
             -- writeEnvBtoEnvC envb'
             -- case simplified of
               -- Left m -> return (Left m)
               -- Right newExpr -> return (Right (ValExpr.cstrConst newExpr))
      -- (ValExpr.view -> ValExpr.Vconst _) -> return (Right expr)
      -- _ -> return (Left ("Not a constant expression (\"" ++ showValExpr expr ++ "\")!"))
-- -- simplifyExpr

-- filterEnvCtoEnvB :: IOC.IOC IOB.EnvB
-- filterEnvCtoEnvB = do
     -- envc <- MonadState.get
     -- case IOC.state envc of
       -- IOC.Noning
         -- -> return IOB.EnvB { IOB.smts     = Map.empty
                            -- , IOB.tdefs    = TxsDefs.empty
                            -- , IOB.sigs     = Sigs.empty
                            -- , IOB.stateid  = 0
                            -- , IOB.params   = IOC.params envc
                            -- , IOB.unid     = IOC.unid envc
                            -- , IOB.msgs     = []
                            -- }
       -- IOC.Initing{..}
         -- -> return IOB.EnvB { IOB.smts     = smts
                            -- , IOB.tdefs    = tdefs
                            -- , IOB.sigs     = sigs
                            -- , IOB.stateid  = 0
                            -- , IOB.params   = IOC.params envc
                            -- , IOB.unid     = IOC.unid envc
                            -- , IOB.msgs     = []
                            -- }
       -- IOC.Testing{..}
         -- -> return IOB.EnvB { IOB.smts     = smts
                            -- , IOB.tdefs    = tdefs
                            -- , IOB.sigs     = sigs
                            -- , IOB.stateid  = curstate
                            -- , IOB.params   = IOC.params envc
                            -- , IOB.unid     = IOC.unid envc
                            -- , IOB.msgs     = []
                            -- }
       -- IOC.Simuling{..}
         -- -> return IOB.EnvB { IOB.smts     = smts
                            -- , IOB.tdefs    = tdefs
                            -- , IOB.sigs     = sigs
                            -- , IOB.stateid  = curstate
                            -- , IOB.params   = IOC.params envc
                            -- , IOB.unid     = IOC.unid envc
                            -- , IOB.msgs     = []
                            -- }
       -- IOC.Stepping{..}
         -- -> return IOB.EnvB { IOB.smts     = smts
                            -- , IOB.tdefs    = tdefs
                            -- , IOB.sigs     = sigs
                            -- , IOB.stateid  = curstate
                            -- , IOB.params   = IOC.params envc
                            -- , IOB.unid     = IOC.unid envc
                            -- , IOB.msgs     = []
                            -- }
-- -- filterEnvCtoEnvB

-- writeEnvBtoEnvC :: IOB.EnvB -> IOC.IOC ()
-- writeEnvBtoEnvC envb = do
    -- putMsgs <- MonadState.gets (IOC.putmsgs . IOC.state)
    -- putMsgs $ IOB.msgs envb
    -- MonadState.modify $ \env -> env { IOC.unid = IOB.unid envb }
-- -- writeEnvBtoEnvC

