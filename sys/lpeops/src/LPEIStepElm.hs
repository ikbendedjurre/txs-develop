{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEIStepElm
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEIStepElm (
iStepElm
) where

import qualified Data.List           as List
import qualified Control.Monad       as Monad
import qualified Data.Set            as Set
import qualified EnvCore             as IOC
import LPEOps
import BlindSubst
import ValExpr hiding (subst)

-- Removes duplicate summands and summands that are unreachable by all other (!) summands
-- (so basically we do a partial, symbolic reachability analysis).
iStepElm :: LPEOperation
iStepElm (tdefs, mdef, (n, channels, initParamEqs, summands)) _out _invariant = do
    let (iStepSummands, nonIStepSummands) = List.partition (\(LPESummand _ offers _ _) -> null offers) (Set.toList summands)
    combinedSummands <- Monad.mapM (combineSummand nonIStepSummands) iStepSummands
    return (Right (tdefs, mdef, (n, channels, initParamEqs, Set.fromList (nonIStepSummands ++ concat combinedSummands))))
  where
    combineSummand :: [LPESummand] -> LPESummand -> IOC.IOC [LPESummand]
    combineSummand nonIStepSummand iStepSummand =
        Monad.mapM (combineTwoSummands iStepSummand) nonIStepSummand
    -- combineSummand
    
    combineTwoSummands :: LPESummand -> LPESummand -> IOC.IOC LPESummand
    combineTwoSummands (LPESummand chanVars1 _ guard1 paramEqs1) summand@(LPESummand chanVars2 chanOffers2 guard2 paramEqs2) = do
        newGuard2 <- doConfidentSubst summand paramEqs1 guard2
        let newGuard = cstrAnd (Set.fromList [guard1, newGuard2])
        newParamEqs <- doConfidentParamEqsSubst summand paramEqs1 paramEqs2
        return (LPESummand (chanVars1 `List.union` chanVars2) chanOffers2 newGuard newParamEqs)
-- iStepElm

