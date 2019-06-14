{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEQComp
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEQComp (
LPEQChild(..),
LPEQCompFunc
) where

import qualified Data.Set as Set
import qualified EnvCore as IOC
import qualified VarId
import qualified TxsDefs

data LPEQChild = LPEQChild { childPC :: VarId.VarId
                           , childVars :: Set.Set VarId.VarId
                           , childBody :: TxsDefs.BExpr
                           }
-- LPEQChild

type LPEQCompFunc = TxsDefs.BExpr -> [LPEQChild] -> IOC.IOC LPEQChild



