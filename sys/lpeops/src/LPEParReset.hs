{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEParReset
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEParReset (
parReset
) where

import qualified Control.Monad       as Monad
import qualified Data.Map            as Map
import qualified Data.List           as List
import qualified Data.Set            as Set
import qualified Data.Text           as Text
import qualified EnvCore             as IOC
import qualified FreeVar
import qualified EnvData
import qualified TxsDefs
import           LPEOps
import           Satisfiability
import           LPEPrettyPrint
import           VarId
import           ValExpr
import           LPESuccessors

--import Debug.Trace

mapGet :: (Show a, Ord a) => Map.Map a b -> a -> b
mapGet m k =
    --trace ("mapGet(" ++ (show k) ++ ")") (
      if Map.member k m
      then m Map.! k
      else error ("Could not find " ++ show k ++ " in map!")
    --)
-- mapGet

mapGetS :: (Show a, Ord a) => LPEProcess -> LPESummand -> Map.Map a b -> a -> b
mapGetS i s m k =
    --trace ("mapGetS(" ++ (show k) ++ ")") (
      if Map.member k m
      then m Map.! k
      else error ("Could not find " ++ show k ++ " in map!\nSummand: " ++ showLPESummand s ++ "\nLPE: " ++ showLPEProcess i)
    --)
-- mapGetS

-- LPE rewrite method.
-- Eliminates parameters that do not contribute to the behavior of a process from an LPE.
-- State spaces before and after are strongly bisimilar.
parReset :: LPEOperation
parReset (tdefs, mdef, process@(_, _channels, paramEqs, summands)) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<parReset>>" ]
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "Identifying successors..." ]
    possibleSuccessors <- Monad.mapM (getPossibleSuccessors summands invariant) (Set.toList summands)
    let successorsPerSummand = zipWith (\s i -> (s, i, Map.keys paramEqs)) (Set.toList summands) possibleSuccessors
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "Analyzing control flow..." ]
    newProcess <- parResetLoop process invariant successorsPerSummand
    return (Right (tdefs, mdef, newProcess))
-- parReset

-- Updates the information collected about summands, in particular their lists of used variables,
-- until the information no longer changes.
-- With the final information, assign ANY values to variables that are unused:
parResetLoop :: LPEProcess -> TxsDefs.VExpr -> [(LPESummand, [LPESummand], [VarId])] -> IOC.IOC LPEProcess
parResetLoop process@(n, channels, initParamEqs, summands) invariant successorsPerSummand = do
    let newSuccessorsPerSummand = parResetUpdate process successorsPerSummand
    if newSuccessorsPerSummand == successorsPerSummand
    then do newSummands <- Monad.mapM (resetParamsInSummand process invariant successorsPerSummand) (Set.toList summands)
            return (n, channels, initParamEqs, Set.fromList newSummands)
    else parResetLoop process invariant newSuccessorsPerSummand
-- parResetLoop

resetParamsInSummand :: LPEProcess -> TxsDefs.VExpr -> [(LPESummand, [LPESummand], [VarId])] -> LPESummand -> IOC.IOC LPESummand
resetParamsInSummand (_, _, initParamEqs, summands) invariant successorsPerSummand summand@(LPESummand channelVars channelOffers guard paramEqs) =
    case [ (sucs, uvars) | (smd, sucs, uvars) <- successorsPerSummand, smd == summand ] of
      [(sucs, uvars)] -> if length uvars == length initParamEqs
                         then return summand -- (All variables are used, apparently, so do not touch the summand.)
                         else do let nonSuccessors = Set.toList (summands Set.\\ Set.fromList sucs)
                                 let newParamEqs = Map.union (Map.filterWithKey (\p _ -> p `elem` uvars) paramEqs) (Map.filterWithKey (\p _ -> p `notElem` uvars) initParamEqs)
                                 constraints <- Monad.mapM (summandToConstraint newParamEqs) nonSuccessors
                                 notSat <- areNotSatisfiable constraints invariant
                                 if notSat
                                 then do printNewParamEqs newParamEqs
                                         return (LPESummand channelVars channelOffers guard newParamEqs)
                                 else return summand
      _ -> return summand
  where
    printNewParamEqs :: LPEParamEqs -> IOC.IOC ()
    printNewParamEqs newParamEqs = do
        let changedParamEqs = Map.filterWithKey (\p v -> v /= mapGet paramEqs p) newParamEqs
        let Just summandNumber = List.elemIndex summand (Set.toList summands)
        Monad.mapM_ (\(p, v) -> IOC.putMsgs [ EnvData.TXS_CORE_ANY ("Setting " ++ Text.unpack (VarId.name p) ++ " to " ++ showValExpr v ++ " instead of " ++ showValExpr (mapGet paramEqs p) ++ " in " ++ numberToString (summandNumber + 1) ++ " summand") ]) (Map.toList changedParamEqs)
    -- printNewParamEqs
    
    summandToConstraint :: LPEParamEqs -> LPESummand -> IOC.IOC TxsDefs.VExpr
    summandToConstraint newParamEqs (LPESummand _ _ g _) = do
        g' <- doBlindSubst newParamEqs g
        return (cstrAnd (Set.fromList [guard, g']))
    -- summandToConstraint
    
    numberToString :: Int -> String
    numberToString number =
        show number ++
        (case number `mod` 10 of
          1 -> "st"
          2 -> "nd"
          3 -> "rd"
          _ -> "th")
    -- numberToString
-- resetParamsInSummand

-- Updates the information collected about summands, in particular their lists of used variables:
parResetUpdate :: LPEProcess -> [(LPESummand, [LPESummand], [VarId])] -> [(LPESummand, [LPESummand], [VarId])]
parResetUpdate i successorsPerSummand = map updateSummand successorsPerSummand
  where
    -- Initially, all variables are added to the list of used variables of a summand.
    -- They are removed only if:
    --  * They occur in the condition of the summand while not being defined as a communication variable, e.g. "CHANNEL ? x"; or
    --  * They are used in the assignment to a variable that IS used by a potential successor summand.
    updateSummand :: (LPESummand, [LPESummand], [VarId]) -> (LPESummand, [LPESummand], [VarId])
    updateSummand (summand, successors, _usedVars) =
        let relevantToSuccessorVars = Set.unions (map getRelevantToSuccessorVars successors) in
          (summand, successors, Set.toList relevantToSuccessorVars)
    
    getRelevantToSuccessorVars :: LPESummand -> Set.Set VarId
    getRelevantToSuccessorVars successor@(LPESummand channelVars _channelOffers guard paramEqs) =
        let usedVars = concat [uvars | (s, _g, uvars) <- successorsPerSummand, s == successor] in
        
        -- Parameters in the guard are relevant to the successor, because they enable/disable the channel+instantiation:
        let guardVars = Set.fromList (FreeVar.freeVars guard) in
        
        -- Parameters used in assignments to used variables are relevant (because the variables are used):
        let assignmentVars = Set.fromList (concat [FreeVar.freeVars (mapGetS i successor paramEqs u) | u <- usedVars]) in
        
        -- Combine them all, but ignore communication variables:
        let allVars = Set.union guardVars assignmentVars in
          allVars Set.\\ Set.fromList channelVars
-- parResetUpdate

