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
-- import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ChanId
-- import qualified SortId
import qualified VarId
import qualified ValExpr
import LPETypes
import LPEBlindSubst
-- import LPESuccessors
import LPEDeterminism
import UntilFixpoint
import VarFactory

-- Makes the LPE deterministic by delaying non-deterministic choices by one step until a fixpoint is reached.
determinizeLPE :: LPEOperation
determinizeLPE lpe _out invariant = do
    newLpe <- untilFixpointM (doDetIteration invariant) lpe
    return (Right newLpe)
-- determinizeLPE

doDetIteration :: TxsDefs.VExpr -> LPE -> IOC.IOC LPE
doDetIteration invariant lpe = do
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
        
        paramPerChanVar <- Map.fromList <$> Monad.mapM createVarMapping chanVars3
        
        -- Build summand 1:
        let useChanVars2 = Map.fromList (zipWith (\cv2 cv1 -> (cv1, ValExpr.cstrVar cv2)) chanVars2 chanVars1)
        guard1' <- doConfidentSubst summand1 useChanVars2 (lpeSmdGuard summand1)
        let newSummand1 = summand1 { lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [lpeSmdGuard summand1, ValExpr.cstrNot guard2']) }
        
        -- Build summand 2:
        let useChanVars1 = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) chanVars1 chanVars2)
        guard2' <- doConfidentSubst summand2 useChanVars1 (lpeSmdGuard summand2)
        let newSummand2 = summand2 { lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [lpeSmdGuard summand2, ValExpr.cstrNot guard1']) }
        
        -- Build summand 3:
        let useChanVars3 = Map.map ValExpr.cstrVar chanVar3PerChanVar
        guard1'' <- doConfidentSubst summand1 useChanVars3 (lpeSmdGuard summand1)
        guard2'' <- doConfidentSubst summand2 useChanVars3 (lpeSmdGuard summand2)
        let newSummand3 = LPESummand { lpeSmdVars = Set.fromList chanVars3
                                     , lpeSmdOffers = Map.map (map (\v -> chanVar3PerChanVar Map.! v)) (lpeSmdOffers summand1)
                                     , lpeSmdGuard = ValExpr.cstrAnd (Set.fromList [guard1'', guard2''])
                                     , lpeSmdEqs = Map.empty
                                     }
        
        
        
        let removedSummands = Set.fromList [summand1, summand2]
        let addedSummands = Set.fromList [newSummand1, newSummand2, newSummand3]
        return lpe { lpeSummands = Set.union (lpeSummands lpe Set.\\ removedSummands) addedSummands }
      Nothing -> return lpe
  where
    createVarMapping :: VarId.VarId -> IOC.IOC (VarId.VarId, VarId.VarId)
    createVarMapping varId = do
        freshVar <- createFreshVarFromVar varId
        return (varId, freshVar)
    -- createVarMapping
-- doDetIteration

-- -- Maps channel variables that do not have a key in parameter paramPerChanVar to fresh LPE parameters.
-- -- The new value of parameter paramPerChanVar (with the additional mappings) is returned.
-- -- The LPE uses the freshly created parameters:
-- --   In summands, there are two scenario's:
-- --    - If a channel variable is NOT used, the corresponding fresh LPE parameter is assigned to itself.
-- --    - If a channel variable IS used, its value is assigned to the corresponding fresh LPE parameter.
-- addChanVarsToState :: (LPE, Map.Map VarId.VarId VarId.VarId) -> IOC.IOC (LPE, Map.Map VarId.VarId VarId.VarId)
-- addChanVarsToState (lpe, paramPerChanVar) = do
    -- let allChanVars = Set.unions (map lpeSmdVars (Set.toList (lpeSummands lpe)))
    -- let unmappedChanVars = allChanVars Set.\\ Map.keysSet paramPerChanVar
    -- newVarMappings <- Map.fromList <$> Monad.mapM createVarMapping (Set.toList unmappedChanVars)
    -- let newVars = Set.fromList (Map.elems newVarMappings)
    -- let newLpe = lpe { lpeInitEqs = Map.union (lpeInitEqs lpe) (defaultValueParamEqs newVars)
                     -- , lpeSummands = map (updateSummand newVarMappings newVars) (lpeSummands lpe)
                     -- }
    -- return (newLpe, Map.union paramPerChanVar newVarMappings)
  -- where
    -- createVarMapping :: VarId.VarId -> IOC.IOC (VarId.VarId, VarId.VarId)
    -- createVarMapping varId = do
        -- freshVar <- createFreshVarFromVar varId
        -- return (varId, freshVar)
    -- -- createVarMapping
    
    -- updateSummand :: Map.Map VarId.VarId VarId.VarId -> Set.Set VarId.VarId -> LPESummand -> LPESummand
    -- updateSummand newVarMappings newVars summand =
        -- if Set.disjoint (Map.keysSet newVarMappings)
        -- then summand { selfLoopParamEqs newVars }
        -- else 
-- -- addChanVarsToState

-- -- doDetIteration :: Set.Set LPESummand -> Int -> TxsDefs.VExpr -> IOC.IOC (Set.Set LPESummand)
-- -- doDetIteration summands iterationIndex invariant = do
    -- -- case findNonDeterministicSummand (Set.toList summands) (Set.toList summands) of
      -- -- Just (LPESummand _ _ _ _:coActors) -> do
          -- -- -- let summandsWithoutCoActors = summands `Set.\\` coActors
          -- -- -- let deterministicSummand = 
          -- -- -- let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
          -- -- -- let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
          -- -- return summands
      -- -- Nothing -> return summands
-- -- -- doDetIteration

-- -- determinizeLPE (tdefs, mdef, (n, channels, initParamEqs, summands)) _out invariant = do
    -- -- newSummand <- doDetIteration summands 1 invariant
    -- -- return (Right (tdefs, mdef, (n, channels, initParamEqs, newSummand)))
-- -- determinizeLPE

-- -- doDetIteration :: Set.Set LPESummand -> Int -> TxsDefs.VExpr -> IOC.IOC (Set.Set LPESummand)
-- -- doDetIteration summands iterationIndex invariant = do
    -- -- case findNonDeterministicSummand (Set.toList summands) (Set.toList summands) of
      -- -- Just (LPESummand _ _ _ _:coActors) -> do
          -- -- -- let summandsWithoutCoActors = summands `Set.\\` coActors
          -- -- -- let deterministicSummand = 
          -- -- -- let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
          -- -- -- let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
          -- -- return summands
      -- -- Nothing -> return summands
-- -- -- doDetIteration

-- -- findNonDeterministicSummand :: [LPESummand] -> [LPESummand] -> TxsDefs.VExpr -> IOC.IOC (Maybe [LPESummand])
-- -- findNonDeterministicSummand _ [] _ = return Nothing
-- -- findNonDeterministicSummand allSummands (uncheckedSummand:uncheckedSummands) invariant = do
    -- -- coActors <- getPossibleCoActors (Set.fromList allSummands) invariant uncheckedSummand
    -- -- if length coActors > 1
    -- -- then return (Just coActors)
    -- -- else findNonDeterministicSummand allSummands uncheckedSummands invariant
-- -- -- findNonDeterministicSummand

-- -- addDeterministicSummands :: [LPESummand] -> [LPESummand] -> VarId.VarId -> TxsDefs.VExpr -> IOC.IOC [LPESummand]
-- -- addDeterministicSummands _ [] _ _ = error "List of non-deterministic summands (co-actors) must consist of at least 2 elements (found 0)!"
-- -- addDeterministicSummands _ [_] _ _ = error "List of non-deterministic summands (co-actors) must consist of at least 2 elements (found 1)!"
-- -- addDeterministicSummands allSummands coActors@(LPESummand vars1 chans1 guard1 paramEqs1:nonDetSummands) prevSummandParam prevSummandValue = do
    -- -- -- Rewrite the guards of all summands using the channel variables of the first summand:
    -- -- let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
    -- -- guardPerCoActor <- Map.fromList <$> Monad.mapM (\m -> (m, getSummandGuard sortedChans1 m)) nonDetSummands
    
    -- -- -- Generate helper parameters (one per channel variable and one per parameter):
    -- -- let params = Map.keys paramEqs ++ vars1
    -- -- let usedNames = map (Text.unpack VarId.name) params
    -- -- let helperPerParam = Map.fromList <$> generateHelpersPerParam usedNames [] params 0
    
    -- -- -- Store the current value of guards in the helper parameters:
    -- -- let defaultParamEqs = Map.mapWithKey (\k _ -> ValExpr.cstrVar k) paramEqs1
    -- -- let prevSummandParamEqs = Map.insert prevSummandParam (ValExpr.cstrConst prevSummandValue) defaultParamEqs
    -- -- let helperParamEqs = Map.fromList (map (\p -> (helperPerParam Map.! p, ValExpr.cstrVar p)) (Map.keys paramEqs))
    
    -- -- -- This summand is a deterministic combination of the non-deterministic input summands (co-actors):
    -- -- let disjunction = ValExpr.cstrOr (Set.fromList (guard1:Map.elems guardPerCoActor))
    -- -- let disjunctiveSummand = LPESummand vars1 chans1 disjunction (Map.union defaultParamEqs helperParamEqs)
    
    -- -- -- 
    -- -- let allSummandsWithoutCoActors = Set.fromList allSummands Set.\\ Set.fromList coActors
    -- -- Set.toList allSummandsWithoutCoActors
  -- -- where
    -- -- getSummandGuard :: LPEChannelOffers -> LPESummand -> IOC.IOC TxsDefs.VExpr
    -- -- getSummandGuard sortedChans1 (LPESummand _ chans2 guard2 _) = do
        -- -- let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
        -- -- let chanVars1 = concatMap snd sortedChans1
        -- -- let chanVars2 = concatMap snd sortedChans2
        -- -- let subst = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) chanVars1 chanVars2)
        -- -- doBlindSubst subst guard2
    -- -- -- getSummandGuard
    
    -- -- generateHelpersPerParam :: [String] -> [(VarId.VarId, VarId.VarId)] -> [VarId.VarId] -> Int -> IOC.IOC [VarId.VarId]
    -- -- generateHelpersPerParam _ generatedDups [] _ = return generatedDups
    -- -- generateHelpersPerParam usedNames generatedDups (p:remainingParams) attemptIndex = do
        -- -- let attempt = "det$" ++ Text.unpack (VarId.name p) ++ if attemptIndex > 0 then "$" ++ show attemptIndex else ""
        -- -- if List.elem attempt usedNames
        -- -- then generateHelpersPerParam usedNames generatedDups (p:remainingParams) (attemptIndex + 1)
        -- -- else do varUnid <- IOC.newUnid
                -- -- let dup = VarId.VarId { VarId.name = Text.pack n
                                      -- -- , VarId.unid = varUnid
                                      -- -- , VarId.varsort = SortId.sortIdBool
                                      -- -- }
                -- -- generateHelpersPerParam (usedNames ++ [attempt]) (generatedDups ++ [(p, dup)]) remainingParams 0
    -- -- -- generateHelpersPerParam
    
    -- -- getSummandParamEqs :: LPESummand -> LPEParamEqs
    -- -- getSummandParamEqs (LPESummand _ _ _ paramEqs2) = paramEqs2
-- -- -- getDeterministicSummands











