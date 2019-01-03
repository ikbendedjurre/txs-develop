{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  BlindSubst
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}
module BlindSubst (
restoreTdefs,
any2freshVar,
any2defaultValue,
doBlindSubst,
doBlindParamEqSubst,
doBlindParamEqsSubst,
doConfidentSubst,
doConfidentParamEqSubst,
doConfidentParamEqsSubst
) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified EnvData
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs
import qualified SortOf
import Constant hiding (sort)
import VarId
import ValExpr hiding (subst)
import ValExprVisitor
import VarFactory
import ValFactory
import LPETypeDefs
import LPEPrettyPrint

-- Manipulating expressions (e.g. blind substitutions before SAT-solving) may require helper variables.
-- These variables are added to the TorXakis definitions in the environment of the monad.
-- To undo these additions, pass the original definitions to the following helper method:
restoreTdefs :: TxsDefs.TxsDefs -> IOC.IOC ()
restoreTdefs tdefs = do
    state <- MonadState.gets IOC.state
    let newState = state { IOC.tdefs = tdefs }
    MonadState.modify (\env -> env { IOC.state = newState })
-- restoreTdefs

-- Eliminates occurrences of 'ANY <sort>' by substituting fresh, free variables.
-- Also returns the previous TorXakis definitions (so that they can be restored afterwards, see above).
any2freshVar :: TxsDefs.VExpr -> IOC.IOC (TxsDefs.TxsDefs, TxsDefs.VExpr, Set.Set VarId)
any2freshVar expr = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    visitorOutput <- visitValExprM any2FreshVarVisitorM expr
    return (tdefs, expression visitorOutput, customData visitorOutput)
  where
    any2FreshVarVisitorM :: [ValExprVisitorOutput (Set.Set VarId)] -> TxsDefs.VExpr -> IOC.IOC (ValExprVisitorOutput (Set.Set VarId))
    any2FreshVarVisitorM _ (view -> Vconst (Cany sort)) = do
        varId <- createFreshVar sort
        return (ValExprVisitorOutput (cstrVar varId) 1 (Set.singleton varId))
    any2FreshVarVisitorM xs x = do
        vo <- MonadState.liftIO $ tryDefaultValExprVisitor (Set.unions (map customData xs)) xs x
        case vo of
          Left _ -> do varId <- createFreshVar (SortOf.sortOf x)
                       return (ValExprVisitorOutput (cstrVar varId) 1 (Set.singleton varId))
          Right r -> return r
-- any2freshVar

-- Eliminates occurrences of 'ANY <sort>' by substituting default data expressions of the same sort.
any2defaultValue :: TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
any2defaultValue expr = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    return (expression (visitValExpr (any2defaultVisitor tdefs) expr))
  where
    any2defaultVisitor :: TxsDefs.TxsDefs -> [ValExprVisitorOutput ()] -> TxsDefs.VExpr -> ValExprVisitorOutput ()
    any2defaultVisitor tdefs _ (view -> Vconst (Cany sort)) = ValExprVisitorOutput (sort2defaultValue tdefs sort) 1 ()
    any2defaultVisitor _ xs x = defaultValExprVisitor () xs x
-- any2defaultValue

-- Applies a substitution to the given expression, introducing 'ANY <sort>' for appearing undefined expressions.
doBlindSubst :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
doBlindSubst subst expr = do
    visitorOutput <- visitValExprM substVisitor expr
    return (expression visitorOutput)
  where
    substVisitor :: [ValExprVisitorOutput ()] -> TxsDefs.VExpr -> IOC.IOC (ValExprVisitorOutput ())
    -- If we find a variable, substitute it (only if it is present in substEqs, of course):
    substVisitor _ (view -> Vvar varId) =
        case Map.lookup varId subst of
          Just v -> return (ValExprVisitorOutput v 1 ())
          Nothing -> return (ValExprVisitorOutput (cstrVar varId) 1 ())
    -- In other cases, reconstruction of the parent expression might fail
    -- (for example because something was substituted incorrectly)
    -- in which case we return 'ANY <sort>' instead:
    substVisitor subExps parentExpr = do
        vo <- MonadState.liftIO $ tryDefaultValExprVisitor () subExps parentExpr
        case vo of
          Left _ -> return (ValExprVisitorOutput (cstrConst (Cany (SortOf.sortOf parentExpr))) 1 ())
          Right r -> return r
-- doBlindSubst

-- Applies 'doBlindSubst' to the value of a key-value pair:
doBlindParamEqSubst :: Map.Map VarId TxsDefs.VExpr -> (VarId, TxsDefs.VExpr) -> IOC.IOC (VarId, TxsDefs.VExpr)
doBlindParamEqSubst subst (varId, expr) = do
    expr' <- doBlindSubst subst expr
    return (varId, expr')
-- doBlindParamEqSubst

-- Applies 'doBlindSubst' to each value of a key-value map:
doBlindParamEqsSubst :: Map.Map VarId TxsDefs.VExpr -> Map.Map VarId TxsDefs.VExpr -> IOC.IOC (Map.Map VarId TxsDefs.VExpr)
doBlindParamEqsSubst subst target = do
    paramEqs <- Monad.mapM (doBlindParamEqSubst subst) (Map.toList target)
    return (Map.fromList paramEqs)
-- doBlindParamEqsSubst

-- Applies a substitution to the given expression, using default data expressions for undefined expressions.
doConfidentSubst :: LPESummand -> Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> IOC.IOC TxsDefs.VExpr
doConfidentSubst contextSummand subst expr = do
    txsdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    visitorOutput <- visitValExprM (substVisitor txsdefs) expr
    return (expression visitorOutput)
  where
    substVisitor :: TxsDefs.TxsDefs -> [ValExprVisitorOutput ()] -> TxsDefs.VExpr -> IOC.IOC (ValExprVisitorOutput ())
    -- If we find a variable, substitute it (only if it is present in substEqs, of course):
    substVisitor _ _ (view -> Vvar varId) =
        case Map.lookup varId subst of
          Just v -> return (ValExprVisitorOutput v 1 ())
          Nothing -> return (ValExprVisitorOutput (cstrVar varId) 1 ())
    -- In other cases, reconstruction of the parent expression might fail
    -- (for example because something was substituted incorrectly)
    -- in which case we return a default data expression of the matching sort instead:
    substVisitor tdefs subExps parentExpr = do
        vo <- MonadState.liftIO $ tryDefaultValExprVisitor () subExps parentExpr
        case vo of
          Left _ -> do let defaultValue = sort2defaultValue tdefs (SortOf.sortOf parentExpr)
                       -- Print a warning, because if this happens we should at least scratch ourselves behind our ears:
                       IOC.putMsgs [ EnvData.TXS_CORE_RUNTIME_WARNING ("WARNING: Confidently substituted " ++ showValExpr defaultValue ++ " for " ++ showValExpr parentExpr ++ showSubst subst
                                       ++ "\nExpression: " ++ showValExpr expr
                                       ++ "\nSummand: " ++ showLPESummand contextSummand) ]
                       return (ValExprVisitorOutput defaultValue 1 ())
          Right r -> return r
-- doConfidentSubst

-- Applies 'doConfidentSubst' to the value of a key-value pair:
doConfidentParamEqSubst :: LPESummand -> Map.Map VarId TxsDefs.VExpr -> (VarId, TxsDefs.VExpr) -> IOC.IOC (VarId, TxsDefs.VExpr)
doConfidentParamEqSubst summand subst (varId, expr) = do
    expr' <- doConfidentSubst summand subst expr
    return (varId, expr')
-- doConfidentParamEqSubst

-- Applies 'doConfidentSubst' to each value of a key-value map:
doConfidentParamEqsSubst :: LPESummand -> Map.Map VarId TxsDefs.VExpr -> Map.Map VarId TxsDefs.VExpr -> IOC.IOC (Map.Map VarId TxsDefs.VExpr)
doConfidentParamEqsSubst summand subst target = do
    paramEqs <- Monad.mapM (doConfidentParamEqSubst summand subst) (Map.toList target)
    return (Map.fromList paramEqs)
-- doConfidentParamEqsSubst



