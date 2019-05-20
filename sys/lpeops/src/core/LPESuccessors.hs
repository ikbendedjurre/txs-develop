{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPESuccessors
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPESuccessors (
isPossibleSuccessor,
getPossibleSuccessors,
LPEPossibleSuccessorMap,
getPossibleSuccessorMap,
isDefiniteSuccessor,
getDefiniteSuccessors,
isPossiblePredecessor,
getPossiblePredecessors,
couldHavePredecessor
) where

import qualified Control.Monad       as Monad
import qualified Data.List           as List
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified Satisfiability      as Sat
import qualified TxsDefs
import qualified ValExpr
import           LPETypes
import           BlindSubst
import           VarFactory

isPossibleSuccessor :: LPESummand -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
isPossibleSuccessor summand invariant candidate = do
    freshVarPerCommVar <- createFreshVars (lpeSmdVarSet candidate)
    g1 <- doBlindSubst (Map.map ValExpr.cstrVar freshVarPerCommVar) (lpeSmdGuard candidate)
    g2 <- doBlindSubst (lpeSmdEqs summand) g1
    let g3 = ValExpr.cstrAnd (Set.fromList [lpeSmdGuard summand, g2])
    Sat.couldBeSatisfiable g3 invariant
-- isPossibleSuccessor

-- Selects all potential successors summands of a given summand from a list with all summands.
-- (In actuality, an overapproximation of all potential successors is selected, namely those
-- whose guard can be satisfied after the guard of the current summand has been satisfied and
-- after the substitutions of the process recursion have taken place.)
getPossibleSuccessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossibleSuccessors summands invariant summand =
    Monad.filterM (isPossibleSuccessor summand invariant) (Set.toList summands)
-- getPossibleSuccessors

type LPEPossibleSuccessorMap = Map.Map LPESummand (Set.Set LPESummand)

getPossibleSuccessorMap :: LPE -> TxsDefs.VExpr -> IOC.IOC LPEPossibleSuccessorMap
getPossibleSuccessorMap lpe invariant =
    Map.fromList <$> Monad.mapM getKeyValuePair (Set.toList (lpeSummands lpe))
  where
    getKeyValuePair :: LPESummand -> IOC.IOC (LPESummand, Set.Set LPESummand)
    getKeyValuePair summand = do
      value <- Set.fromList <$> getPossibleSuccessors (lpeSummands lpe) invariant summand
      return (summand, value)
-- getPossibleSuccessors

isDefiniteSuccessor :: LPESummand -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
isDefiniteSuccessor summand invariant candidate = do
    g3 <- doBlindSubst (lpeSmdEqs summand) (lpeSmdGuard candidate)
    Sat.isTautology g3 invariant
-- isDefiniteSuccessor

-- Selects all summands from a given list that are definitely successors of a given summand.
-- The result is an underapproximation!
getDefiniteSuccessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getDefiniteSuccessors summands invariant summand =
    Monad.filterM (isDefiniteSuccessor summand invariant) (Set.toList summands)
-- getDefiniteSuccessors

isPossiblePredecessor :: LPESummand -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
isPossiblePredecessor summand invariant candidate = isPossibleSuccessor candidate invariant summand

getPossiblePredecessors :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC [LPESummand]
getPossiblePredecessors summands invariant summand =
    Monad.filterM (isPossiblePredecessor summand invariant) (Set.toList summands)
-- getPossiblePredecessors

couldHavePredecessor :: LPESummands -> TxsDefs.VExpr -> LPESummand -> IOC.IOC Bool
couldHavePredecessor summands invariant summand = do
    preds <- getPossiblePredecessors summands invariant summand
    return (not (List.null preds))
-- couldHavePredecessor

