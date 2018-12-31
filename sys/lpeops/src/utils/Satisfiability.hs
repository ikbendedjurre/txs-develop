{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Satisfiability
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module Satisfiability (
getSomeSolution,
isTautology,
isSatisfiable,
couldBeSatisfiable,
isNotSatisfiable,
areSatisfiable,
areNotSatisfiable,
getUniqueSolution,
showSolution,
defaultInvariant,
module BlindSubst
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified EnvData
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified FreeVar
import qualified Solve
import qualified SortId
import qualified SortOf
import qualified SolveDefs
import qualified TxsDefs
import qualified Constant
import VarId
import ValExpr
import BlindSubst
import LPEPrettyPrint
import ValFactory

-- Frequently used method; code is modified code from TxsCore (with several safety checks removed!!).
-- Attempts to find a solution for the given expression.
-- If a solution is found, it consists of a map with one value for each of the specified variables.
getSomeSolution :: TxsDefs.VExpr -> TxsDefs.VExpr -> [VarId] -> IOC.IOC (SolveDefs.SolveProblem VarId)
getSomeSolution expr _invariant variables =
    if SortOf.sortOf expr /= SortId.sortIdBool
    then do IOC.putMsgs [ EnvData.TXS_CORE_USER_ERROR ("Value expression must be of sort Bool (" ++ show expr ++ ")!") ]
            return SolveDefs.UnableToSolve
    else do smtEnv <- IOC.getSMT "current"
            (tdefs, expr1, undefs) <- eliminateAny expr
            --IOC.putMsgs [ EnvData.TXS_CORE_ANY ("expr1 = " ++ showContextFreeValExpr expr1) ]
            let freeVars1 = Set.union (Set.fromList (FreeVar.freeVars expr1 ++ variables)) undefs
            let assertions1 = Solve.add expr1 Solve.empty
            (sol1, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve (Set.toList freeVars1) assertions1) smtEnv
            case sol1 of
              SolveDefs.Solved solMap ->
                if undefs == Set.empty
                then do restoreTdefs tdefs
                        return (buildSolution tdefs solMap)
                else do let freeVars2 = undefs
                        let blindSubstVars = Set.toList (freeVars1 Set.\\ freeVars2)
                        let blindSubst = Map.fromList (map (\v -> (v, cstrConst (solMap Map.! v))) blindSubstVars)
                        expr2 <- doBlindSubst blindSubst expr1
                        --IOC.putMsgs [ EnvData.TXS_CORE_ANY ("expr2 = " ++ showContextFreeValExpr expr2) ]
                        let assertions2 = Solve.add (cstrNot expr2) Solve.empty
                        (sol2, _) <- MonadState.lift $ MonadState.runStateT (Solve.solve (Set.toList freeVars2) assertions2) smtEnv
                        case sol2 of
                          SolveDefs.Unsolvable -> do restoreTdefs tdefs
                                                     return (buildSolution tdefs solMap)
                          _ -> do restoreTdefs tdefs
                                  return SolveDefs.UnableToSolve
              otherResult -> do restoreTdefs tdefs
                                return otherResult
  where
    buildSolution :: TxsDefs.TxsDefs -> Map.Map VarId Constant.Constant -> SolveDefs.SolveProblem VarId
    buildSolution tdefs solMap = SolveDefs.Solved (Map.fromList (map (\v -> (v, Map.findWithDefault (sort2defaultConst tdefs (SortOf.sortOf v)) v solMap)) variables))
-- getSomeSolution

defaultInvariant :: TxsDefs.VExpr
defaultInvariant = cstrConst (Constant.Cbool True)

-- Checks if the specified expression cannot be false.
isTautology :: TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC Bool
isTautology expr = isNotSatisfiable (cstrNot expr)

-- Checks if a solution for the specified expression might exist.
couldBeSatisfiable :: TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC Bool
couldBeSatisfiable expr invariant = do
    sol <- getSomeSolution expr invariant []
    case sol of
      SolveDefs.Unsolvable -> return False
      _ -> return True
-- couldBeSatisfiable

-- Checks if a solution for the specified expression definitely exists.
isSatisfiable :: TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC Bool
isSatisfiable expr invariant = do
    sol <- getSomeSolution expr invariant []
    case sol of
      SolveDefs.Solved _ -> return True
      _ -> return False
-- isSatisfiable

-- Checks if the specified expression cannot be true.
isNotSatisfiable :: TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC Bool
isNotSatisfiable expr invariant = do
    sol <- getSomeSolution expr invariant []
    return (sol == SolveDefs.Unsolvable)
-- isNotSatisfiable

-- Checks if all specified expressions could be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, X == 1] would yield true!
areSatisfiable :: [TxsDefs.VExpr] -> TxsDefs.VExpr -> IOC.IOC Bool
areSatisfiable expressions invariant = do sat <- Monad.mapM (`isSatisfiable` invariant) expressions
                                          return (List.and sat)
-- areSatisfiable

-- Checks if none of the specified expressions not be true.
-- Note that each expression is considered in a vacuum, e.g. input [X == 0, false] would yield false!
areNotSatisfiable :: [TxsDefs.VExpr] -> TxsDefs.VExpr -> IOC.IOC Bool
areNotSatisfiable expressions invariant = do sat <- Monad.mapM (`isNotSatisfiable` invariant) expressions
                                             return (List.and sat)
-- areNotSatisfiable

-- Attempts to find a unique solution for the given expression.
-- The solution only has to be unique with regard to the variables listed by the third parameter:
getUniqueSolution :: TxsDefs.VExpr -> TxsDefs.VExpr -> [VarId] -> [VarId] -> IOC.IOC (SolveDefs.SolveProblem VarId)
getUniqueSolution expr invariant variables uniqueSolVars = do
    sol <- getSomeSolution expr invariant (variables ++ uniqueSolVars)
    case sol of
      SolveDefs.Solved solMap ->
        do -- Then check if there is NO solution where (one of) the specified variables have different values:
           let extraConditions = map (\v -> cstrEqual (cstrVar v) (cstrConst (solMap Map.! v))) uniqueSolVars
           let restrictedExpression = cstrAnd (Set.fromList [expr, cstrNot (cstrAnd (Set.fromList extraConditions))])
           unsat <- isNotSatisfiable restrictedExpression invariant
           -- If so, the solution is unique (w.r.t. the specified variables):
           return (if unsat then sol else SolveDefs.UnableToSolve)
      _ -> return sol
-- getUniqueSolution

showSolution :: SolveDefs.SolveProblem VarId -> String
showSolution SolveDefs.Unsolvable = "Unsolvable"
showSolution SolveDefs.UnableToSolve = "UnableToSolve"
showSolution (SolveDefs.Solved solMap) =
    let f (p, v) = Text.unpack (VarId.name p) ++ " := " ++ showValExpr (cstrConst v) in
      "Solved [" ++ List.intercalate ", " (map f (Map.toList solMap)) ++ "]"
-- showSolution








