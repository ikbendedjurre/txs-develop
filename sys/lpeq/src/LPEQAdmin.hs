{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEQAdmin
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEQAdmin (
AdminData(..),
addToFinished,
addToQueued,
addToFailed
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified TxsDefs

data AdminData = AdminData { inChans :: Set.Set TxsDefs.ChanId
                           , outChans :: Set.Set TxsDefs.ChanId
                           , newProcs :: Map.Map TxsDefs.ProcId TxsDefs.ProcDef
                           , finished :: Map.Map TxsDefs.BExpr TxsDefs.BExpr
                           , queued :: Set.Set TxsDefs.BExpr
                           , failed :: Set.Set TxsDefs.BExpr
                           }
-- AdminData

addToFinished :: TxsDefs.BExpr -> TxsDefs.BExpr -> AdminData -> AdminData
addToFinished bexpr1 bexpr2 adminData = adminData { finished = Map.insert bexpr1 bexpr2 (finished adminData) }

addToQueued :: TxsDefs.BExpr -> AdminData -> AdminData
addToQueued bexpr adminData = adminData { queued = Set.insert bexpr (queued adminData) }

addToFailed :: TxsDefs.BExpr -> AdminData -> AdminData
addToFailed bexpr adminData = adminData { failed = Set.insert bexpr (failed adminData) }

