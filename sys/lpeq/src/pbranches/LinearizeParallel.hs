{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LinearizeParallel
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module LinearizeParallel (
linearize
) where

import qualified Data.Set as Set
-- import qualified EnvCore as IOC
import qualified TxsDefs
import qualified TxsShow
-- import qualified ProcId
-- import qualified ProcDef
import BehExprDefs

import PBranchUtils

linearize :: PBranchLinearizer
linearize _g (TxsDefs.view -> Parallel cidSet bexprs) = do
    return (parallel cidSet bexprs, Set.empty, [])
linearize _ bexpr = error ("Behavioral expression not accounted for (\"" ++ TxsShow.fshow bexpr ++ "\")!")

