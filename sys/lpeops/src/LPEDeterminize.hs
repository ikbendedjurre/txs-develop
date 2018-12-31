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

-- import qualified Data.List as List
-- import qualified Data.Map as Map
-- import qualified Control.Monad as Monad
-- import qualified Data.Set as Set
-- import qualified Data.Text as Text
-- import qualified EnvCore as IOC
-- import qualified TxsDefs
-- import qualified ChanId
-- import qualified SortId
-- import qualified VarId
-- import qualified ValExpr
import LPEOps
-- import BlindSubst
-- import LPESuccessors

-- Makes the LPE deterministic by delaying non-deterministic choices by one step until a fixpoint is reached.
determinizeLPE :: LPEOperation
determinizeLPE x _out _invariant = return (Right x)
-- determinizeLPE (tdefs, mdef, (n, channels, initParamEqs, summands)) _out invariant = do
    -- newSummand <- doDetIteration summands 1 invariant
    -- return (Right (tdefs, mdef, (n, channels, initParamEqs, newSummand)))
-- determinizeLPE

-- doDetIteration :: Set.Set LPESummand -> Int -> TxsDefs.VExpr -> IOC.IOC (Set.Set LPESummand)
-- doDetIteration summands iterationIndex invariant = do
    -- case findNonDeterministicSummand (Set.toList summands) (Set.toList summands) of
      -- Just (LPESummand _ _ _ _:coActors) -> do
          -- -- let summandsWithoutCoActors = summands `Set.\\` coActors
          -- -- let deterministicSummand = 
          -- -- let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
          -- -- let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
          -- return summands
      -- Nothing -> return summands
-- -- doDetIteration

-- findNonDeterministicSummand :: [LPESummand] -> [LPESummand] -> TxsDefs.VExpr -> IOC.IOC (Maybe [LPESummand])
-- findNonDeterministicSummand _ [] _ = return Nothing
-- findNonDeterministicSummand allSummands (uncheckedSummand:uncheckedSummands) invariant = do
    -- coActors <- getPossibleCoActors (Set.fromList allSummands) invariant uncheckedSummand
    -- if length coActors > 1
    -- then return (Just coActors)
    -- else findNonDeterministicSummand allSummands uncheckedSummands invariant
-- -- findNonDeterministicSummand

-- addDeterministicSummands :: [LPESummand] -> [LPESummand] -> VarId.VarId -> TxsDefs.VExpr -> IOC.IOC [LPESummand]
-- addDeterministicSummands _ [] _ _ = error "List of non-deterministic summands (co-actors) must consist of at least 2 elements (found 0)!"
-- addDeterministicSummands _ [_] _ _ = error "List of non-deterministic summands (co-actors) must consist of at least 2 elements (found 1)!"
-- addDeterministicSummands allSummands coActors@(LPESummand vars1 chans1 guard1 paramEqs1:nonDetSummands) prevSummandParam prevSummandValue = do
    -- -- Rewrite the guards of all summands using the channel variables of the first summand:
    -- let sortedChans1 = List.sortOn (ChanId.unid . fst) chans1
    -- guardPerCoActor <- Map.fromList <$> Monad.mapM (\m -> (m, getSummandGuard sortedChans1 m)) nonDetSummands
    
    -- -- Generate helper parameters (one per channel variable and one per parameter):
    -- let params = Map.keys paramEqs ++ vars1
    -- let usedNames = map (Text.unpack VarId.name) params
    -- let helperPerParam = Map.fromList <$> generateHelpersPerParam usedNames [] params 0
    
    -- -- Store the current value of guards in the helper parameters:
    -- let defaultParamEqs = Map.mapWithKey (\k _ -> ValExpr.cstrVar k) paramEqs1
    -- let prevSummandParamEqs = Map.insert prevSummandParam (ValExpr.cstrConst prevSummandValue) defaultParamEqs
    -- let helperParamEqs = Map.fromList (map (\p -> (helperPerParam Map.! p, ValExpr.cstrVar p)) (Map.keys paramEqs))
    
    -- -- This summand is a deterministic combination of the non-deterministic input summands (co-actors):
    -- let disjunction = ValExpr.cstrOr (Set.fromList (guard1:Map.elems guardPerCoActor))
    -- let disjunctiveSummand = LPESummand vars1 chans1 disjunction (Map.union defaultParamEqs helperParamEqs)
    
    -- -- 
    -- let allSummandsWithoutCoActors = Set.fromList allSummands Set.\\ Set.fromList coActors
    -- Set.toList allSummandsWithoutCoActors
  -- where
    -- getSummandGuard :: LPEChannelOffers -> LPESummand -> IOC.IOC TxsDefs.VExpr
    -- getSummandGuard sortedChans1 (LPESummand _ chans2 guard2 _) = do
        -- let sortedChans2 = List.sortOn (ChanId.unid . fst) chans2
        -- let chanVars1 = concatMap snd sortedChans1
        -- let chanVars2 = concatMap snd sortedChans2
        -- let subst = Map.fromList (zipWith (\cv1 cv2 -> (cv2, ValExpr.cstrVar cv1)) chanVars1 chanVars2)
        -- doBlindSubst subst guard2
    -- -- getSummandGuard
    
    -- generateHelpersPerParam :: [String] -> [(VarId.VarId, VarId.VarId)] -> [VarId.VarId] -> Int -> IOC.IOC [VarId.VarId]
    -- generateHelpersPerParam _ generatedDups [] _ = return generatedDups
    -- generateHelpersPerParam usedNames generatedDups (p:remainingParams) attemptIndex = do
        -- let attempt = "det$" ++ Text.unpack (VarId.name p) ++ if attemptIndex > 0 then "$" ++ show attemptIndex else ""
        -- if List.elem attempt usedNames
        -- then generateHelpersPerParam usedNames generatedDups (p:remainingParams) (attemptIndex + 1)
        -- else do varUnid <- IOC.newUnid
                -- let dup = VarId.VarId { VarId.name = Text.pack n
                                      -- , VarId.unid = varUnid
                                      -- , VarId.varsort = SortId.sortIdBool
                                      -- }
                -- generateHelpersPerParam (usedNames ++ [attempt]) (generatedDups ++ [(p, dup)]) remainingParams 0
    -- -- generateHelpersPerParam
    
    -- getSummandParamEqs :: LPESummand -> LPEParamEqs
    -- getSummandParamEqs (LPESummand _ _ _ paramEqs2) = paramEqs2
-- -- getDeterministicSummands











