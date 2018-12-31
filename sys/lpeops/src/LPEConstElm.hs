{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEConstElm
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module LPEConstElm (
constElm
) where

import qualified Control.Monad       as Monad
import qualified Data.Map            as Map
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import qualified EnvData
import qualified TxsDefs
import           LPEOps
import           LPEParRemoval
import           Satisfiability
import           VarId
import           ValExpr hiding (subst)
import           Constant

-- LPE rewrite method.
-- Eliminates parameters that always have the same value from an LPE.
constElm :: LPEOperation
constElm (tdefs, mdef, process@(_, _, initParamEqs, _)) _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<constElm>>" ]
    constParams <- getConstParams process invariant (Map.keysSet initParamEqs)
    newProcess <- removeParsFromLPE constParams process
    return (Right (tdefs, mdef, newProcess))
-- constElm

getConstParams :: LPEProcess -> TxsDefs.VExpr -> Set.Set VarId -> IOC.IOC (Set.Set VarId)
getConstParams process invariant constParams = do
    newConstParams <- getConstParamsForAllSummands process invariant constParams
    if newConstParams /= constParams
    then getConstParams process invariant newConstParams
    else return newConstParams
-- getConstParams

getConstParamsForAllSummands :: LPEProcess -> TxsDefs.VExpr -> Set.Set VarId -> IOC.IOC (Set.Set VarId)
getConstParamsForAllSummands (_, _, initParamEqs, summands) invariant constParams = do
    let subst = Map.restrictKeys initParamEqs constParams
    constParamsPerSummand <- Monad.mapM (getConstParamsForSummand subst invariant constParams) (Set.toList summands)
    return (foldl Set.intersection constParams constParamsPerSummand)
-- getConstParamsForAllSummands

getConstParamsForSummand :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> Set.Set VarId -> LPESummand -> IOC.IOC (Set.Set VarId)
getConstParamsForSummand subst invariant constParams summand = do
    result <- Monad.mapM (isConstParamForSummand subst invariant summand) (Set.toList constParams)
    return (Set.unions result)
-- getConstParamsForSummand

isConstParamForSummand :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> LPESummand -> VarId -> IOC.IOC (Set.Set VarId)
isConstParamForSummand subst invariant (LPESummand _ _ guard paramEqs) testParam = do
    let expr = cstrITE guard (cstrEqual (paramEqs Map.! testParam) (cstrVar testParam)) (cstrConst (Cbool True))
    expr' <- doBlindSubst subst expr
    taut <- isTautology expr' invariant
    if taut
    then return (Set.singleton testParam)
    else return Set.empty
-- isConstParamsForSummand


