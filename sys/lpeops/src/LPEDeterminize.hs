{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEDeterminize
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEDeterminize (
determinizeLPE
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Set as Set
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import qualified ChanId
import qualified VarId
import qualified ValExpr
import qualified Constant
import LPETypes
import LPEBlindSubst
import LPESuccessors
import LPEDeterminism
import UntilFixpoint
import VarFactory

-- Makes the LPE deterministic by delaying non-deterministic choices by one step until a fixpoint is reached.
determinizeLPE :: LPEOperation
determinizeLPE lpe _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<det>>" ]
    newLpe <- untilFixpointM (doDetIteration invariant) lpe
    return (Right newLpe)
-- determinizeLPE

doDetIteration :: TxsDefs.VExpr -> LPE -> IOC.IOC LPE
doDetIteration invariant lpe = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Looking for non-deterministic summand pair in " ++ show (Set.size (lpeSummands lpe)) ++ " summands...") ]
    -- Find a pair of non-deterministic summands:
    nothingOrNonDetPair <- getNonDeterministicSummandPair invariant (Set.toList (lpeSummands lpe))
    case nothingOrNonDetPair of
      Just (summand1, summand2) -> do
        let sortedChans1 = List.sortOn (ChanId.unid . fst) (Map.toList (lpeSmdOffers summand1))
        let sortedChans2 = List.sortOn (ChanId.unid . fst) (Map.toList (lpeSmdOffers summand2))
        let chanVars1 = concatMap snd sortedChans1
        let chanVars2 = concatMap snd sortedChans2
        
        chanVar3PerChanVar <- Map.fromList <$> Monad.mapM createVarMapping (chanVars1 ++ chanVars2)
        let chanVars3 = Map.elems chanVar3PerChanVar
        
        chanVar3PerParam <- Map.fromList <$> Monad.mapM createParMapping chanVars3
        nonDetFlagVar <- createFreshBoolVarFromPrefix "__NDF"
        
        -- All summands other than summand1 and summand2 are disabled after summand3, because
        -- they do not compensate for the fact that summand3 did not do a state update according to summand1 or summand2.
        -- First initialize some preparatory variables:
        let disableGuard = ValExpr.cstrEqual (ValExpr.cstrVar nonDetFlagVar) (ValExpr.cstrConst (Constant.Cbool False))
        let extraSmdEqs = Map.insert nonDetFlagVar (ValExpr.cstrConst (Constant.Cbool False)) (selfLoopParamEqs (Map.keysSet chanVar3PerParam))
        let disableSmd = getDisabledSummand disableGuard extraSmdEqs
        
        -- Build 'the disabled summands' here:
        let disabledSummands = map disableSmd (Set.toList (lpeSummands lpe Set.\\ Set.fromList [summand1, summand2]))
        
        -- Build summand 1.
        -- Summand 1 requires that summand1 is enabled and that summand2 is disabled.
        -- Summand 1 is also disabled immediately after summand 3.
        --
        -- When enabled, summand 1 follows the original behavior of summand1.
        -- (No fresh communication variables are created because summand1 is not part of the new LPE.)
        let useChanVars1 = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) chanVars1 chanVars2)
        guard2' <- doConfidentSubst summand2 useChanVars1 (lpeSmdGuard summand2)
        let newSummand1 = disableSmd (summand1 { lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [lpeSmdGuard summand1, ValExpr.cstrNot guard2']) })
        
        -- Build summand 2.
        -- Summand 2 requires that summand2 is enabled and that summand1 is disabled.
        -- Summand 2 is also disabled immediately after summand 3.
        --
        -- When enabled, summand 2 follows the original behavior of summand2.
        -- (No fresh communication variables are created because summand2 is not part of the new LPE.)
        let useChanVars2 = Map.fromList (zipWith (\cv2 cv1 -> (cv1, ValExpr.cstrVar cv2)) chanVars2 chanVars1)
        guard1' <- doConfidentSubst summand1 useChanVars2 (lpeSmdGuard summand1)
        let newSummand2 = disableSmd (summand2 { lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [lpeSmdGuard summand2, ValExpr.cstrNot guard1']) })
        
        -- Build summand 3.
        -- Summand 3 requires that summand1 and summand2 are enabled simultaneously.
        --
        -- It also captures any communicated values in freshly created communication variables.
        -- The communicated values are subsequently stored in freshly created parameters, and
        -- the values of the original parameters are not changed;
        -- this makes it possible to delay the decision between summand1 and summand2.
        --
        -- Finally, summand 3 sets a freshly created flag variable to true.
        -- This flag enables the modified potential-successor summands that we create below, and
        -- disables all other summands (as described above).
        let useChanVars3 = Map.map ValExpr.cstrVar chanVar3PerChanVar
        guard1'' <- doConfidentSubst summand1 useChanVars3 (lpeSmdGuard summand1)
        guard2'' <- doConfidentSubst summand2 useChanVars3 (lpeSmdGuard summand2)
        let newSummand3 = LPESummand { lpeSmdVars = Set.fromList chanVars3
                                     , lpeSmdOffers = Map.map (map (\v -> chanVar3PerChanVar Map.! v)) (lpeSmdOffers summand1)
                                     , lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [disableGuard, guard1'', guard2''])
                                     , lpeSmdEqs =
                                         Map.union
                                           -- Set the non-determinism flag to true, and do not change the original parameters:
                                           (Map.insert nonDetFlagVar (ValExpr.cstrConst (Constant.Cbool True)) (selfLoopParamEqs (lpeParams lpe)))
                                           -- Store the communicated values in the freshly created parameters:
                                           (Map.map ValExpr.cstrVar chanVar3PerParam)
                                     }
        
        -- Summands that potentially succeed summand1 or summand2 are potentially successors of the constructed summand 3 as well.
        -- They must therefore be enabled immediately after summand 3.
        -- They must also apply the parameter assignments of summand1 or summand2 in their guard, since summand 3 did not do this.
        let enableGuard = ValExpr.cstrEqual (ValExpr.cstrVar nonDetFlagVar) (ValExpr.cstrConst (Constant.Cbool True))
        let useParams = Map.fromList (map (\p -> (chanVar3PerParam Map.! p, ValExpr.cstrVar p)) (Map.keys chanVar3PerParam))
        let getEnabledSmd = getEnabledSummand enableGuard useParams extraSmdEqs
        
        -- Build the enabled summands (for both summand1 and summand2):
        possibleSuccessors1 <- getPossibleSuccessors (lpeSummands lpe) invariant summand1
        possibleSuccessors2 <- getPossibleSuccessors (lpeSummands lpe) invariant summand2
        enabledSummands1 <- Monad.mapM getEnabledSmd possibleSuccessors1
        enabledSummands2 <- Monad.mapM getEnabledSmd possibleSuccessors2
        
        IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Added " ++ show (length enabledSummands1 + length enabledSummands2 + 1) ++ " summands to LPE") ]
        
        -- Combine everything:
        return lpe { lpeInitEqs = Map.union
                                    -- Set the non-determinism flag to true, and add it to the original parameters:
                                    (Map.insert nonDetFlagVar (ValExpr.cstrConst (Constant.Cbool False)) (lpeInitEqs lpe))
                                    -- Set newly created parameters to a default value:
                                    (defaultValueParamEqs (lpeContext lpe) (Map.keysSet chanVar3PerParam))
                   , lpeSummands = Set.fromList (disabledSummands ++ [newSummand1, newSummand2, newSummand3] ++ enabledSummands1 ++ enabledSummands2) }
      Nothing -> return lpe
  where
    createVarMapping :: VarId.VarId -> IOC.IOC (VarId.VarId, VarId.VarId)
    createVarMapping varId = do
        freshVar <- createFreshVarFromVar varId
        return (varId, freshVar)
    -- createVarMapping
    
    createParMapping :: VarId.VarId -> IOC.IOC (VarId.VarId, VarId.VarId)
    createParMapping varId = do
        freshPar <- createFreshVarFromVar varId
        return (freshPar, varId)
    -- createParMapping
    
    getDisabledSummand :: TxsDefs.VExpr -> LPEParamEqs -> LPESummand -> LPESummand
    getDisabledSummand disableGuard extraSmdEqs summand =
        summand { lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [disableGuard, lpeSmdGuard summand])
                , lpeSmdEqs = Map.union (lpeSmdEqs summand) extraSmdEqs
                }
    -- getDisabledSummand
    
    getEnabledSummand :: TxsDefs.VExpr -> LPEParamEqs -> LPEParamEqs -> LPESummand -> IOC.IOC LPESummand
    getEnabledSummand enableGuard useParams extraSmdEqs summand = do
        g <- doConfidentSubst summand useParams (lpeSmdGuard summand)
        return (summand { lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [enableGuard, g])
                        , lpeSmdEqs = Map.union (lpeSmdEqs summand) extraSmdEqs
                        })
    -- getEnabledSummand
-- doDetIteration

