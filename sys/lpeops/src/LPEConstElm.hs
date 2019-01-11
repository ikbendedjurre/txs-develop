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
import qualified Satisfiability as Sat
import           LPETypes
import           LPEParRemoval
import           VarId
import qualified ValExpr
import           Constant
import           BlindSubst

-- LPE rewrite method.
-- Eliminates parameters that always have the same value from an LPE.
constElm :: LPEOperation
constElm lpe _out invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<constelm>>" ]
    constParams <- getConstParams lpe invariant (Map.keysSet (lpeInitEqs lpe))
    newLpe <- removeParsFromLPE constParams lpe
    return (Right newLpe)
-- constElm

getConstParams :: LPE -> TxsDefs.VExpr -> Set.Set VarId -> IOC.IOC (Set.Set VarId)
getConstParams lpe invariant constParams = do
    newConstParams <- getConstParamsForAllSummands lpe invariant constParams
    if newConstParams /= constParams
    then getConstParams lpe invariant newConstParams
    else return newConstParams
-- getConstParams

getConstParamsForAllSummands :: LPE -> TxsDefs.VExpr -> Set.Set VarId -> IOC.IOC (Set.Set VarId)
getConstParamsForAllSummands lpe invariant constParams = do
    let subst = Map.restrictKeys (lpeInitEqs lpe) constParams
    constParamsPerSummand <- Monad.mapM (getConstParamsForSummand subst invariant constParams) (Set.toList (lpeSummands lpe))
    return (foldl Set.intersection constParams constParamsPerSummand)
-- getConstParamsForAllSummands

getConstParamsForSummand :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> Set.Set VarId -> LPESummand -> IOC.IOC (Set.Set VarId)
getConstParamsForSummand subst invariant constParams summand = do
    result <- Monad.mapM (isConstParamForSummand subst invariant summand) (Set.toList constParams)
    return (Set.unions result)
-- getConstParamsForSummand

isConstParamForSummand :: Map.Map VarId TxsDefs.VExpr -> TxsDefs.VExpr -> LPESummand -> VarId -> IOC.IOC (Set.Set VarId)
isConstParamForSummand subst invariant summand testParam = do
    let expr = ValExpr.cstrITE (lpeSmdGuard summand) (ValExpr.cstrEqual ((lpeSmdEqs summand) Map.! testParam) (ValExpr.cstrVar testParam)) (ValExpr.cstrConst (Cbool True))
    expr' <- doBlindSubst subst expr
    taut <- Sat.isTautology expr' invariant
    if taut
    then return (Set.singleton testParam)
    else return Set.empty
-- isConstParamsForSummand


