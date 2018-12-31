{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEAngelic
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEAngelic (
makeInputEnabledLPE
) where

-- import qualified Data.List as List
-- import qualified Data.Map as Map
-- import qualified Control.Monad as Monad
-- import qualified Data.Set as Set
-- import qualified Data.Text as Text
-- import qualified EnvCore as IOC
-- import qualified TxsDefs
-- import qualified ChanId
-- import qualified SortId
-- import qualified VarId
-- import qualified ValExpr
import LPEOps
-- import BlindSubst
-- import LPESuccessors

-- Makes the LPE deterministic by delaying non-deterministic choices by one step until a fixpoint is reached.
makeInputEnabledLPE :: LPEOperation
makeInputEnabledLPE x _out _invariant = return (Right x)