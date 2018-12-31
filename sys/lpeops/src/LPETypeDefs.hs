{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPETypeDefs
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPETypeDefs (
LPEModel,
LPEProcess,
LPESummand(..),
LPESummands,
LPEChannelOffer,
LPEChannelOffers,
LPEParamEqs,
newLPESummand,
newLPEProcess,
newLPEModel,
paramEqsLookup
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified BehExprDefs
import qualified TxsDefs
import qualified VarId

type LPEModel = (TxsDefs.TxsDefs, TxsDefs.ModelDef, LPEProcess)

-- Type around which this module revolves.
-- It consists of the following parts:
--  - Name of the process.
--  - Channels used by the LPE (included mostly so that conversion to TXS is possible without additional channel information).
--  - Parameters used by the LPE and their initial values (each pair forms a 'parameter equation').
--  - List of summands of the LPE.
type LPEProcess = (Text.Text, [TxsDefs.ChanId], LPEParamEqs, LPESummands)

-- Main building block of an LPE.
-- Each summand provides the following pieces of critical information:
--  - All channel variables, including hidden variables.
--  - Channel offers (action prefices and the *fresh* variables - also found in the earlier list - used per action prefix for synchronization).
--  - Guard (restriction on when the summand can be 'applied').
--  - STOP, or a number of parameter equations to be used for the recursive instantiation.
data LPESummand = LPESummand [VarId.VarId] LPEChannelOffers TxsDefs.VExpr LPEParamEqs deriving (Eq, Ord, Show)
type LPESummands = Set.Set LPESummand

-- Convenience type.
-- Relates a channel with communication variables over which that channel must be synchronized.
type LPEChannelOffer = (TxsDefs.ChanId, [VarId.VarId])
type LPEChannelOffers = [LPEChannelOffer]

-- Convenience type.
-- Relates a parameter with the (initial) value of that parameter
-- (in the case of a particular process instantiation).
type LPEParamEqs = Map.Map VarId.VarId TxsDefs.VExpr

paramEqsLookup :: [VarId.VarId] -> LPEParamEqs -> [TxsDefs.VExpr]
paramEqsLookup orderedParams paramEqs = map fromEqs orderedParams
  where
    fromEqs :: VarId.VarId -> TxsDefs.VExpr
    fromEqs p = case paramEqs Map.!? p of
                  Just e -> e
                  Nothing -> error ("Could not find parameter \"" ++ Text.unpack (VarId.name p) ++ "\" in \"{" ++ List.intercalate ", " (map (Text.unpack . VarId.name) (Map.keys paramEqs)) ++ "}\"!")
-- paramEqsLookup

toLPEParamEqs :: [(VarId.VarId, TxsDefs.VExpr)] -> LPEParamEqs
toLPEParamEqs = Map.fromList

newLPESummand :: [VarId.VarId] -> LPEChannelOffers -> TxsDefs.VExpr -> [(VarId.VarId, TxsDefs.VExpr)] -> LPESummand
newLPESummand chanVarIds chanOffers guard procInstParamEqs = LPESummand chanVarIds chanOffers guard (toLPEParamEqs procInstParamEqs)

newLPEProcess :: ([TxsDefs.ChanId], [(VarId.VarId, TxsDefs.VExpr)], [LPESummand]) -> LPEProcess
newLPEProcess (chanIds, initParamEqs, summands) = (Text.pack "LPE", chanIds, toLPEParamEqs initParamEqs, Set.fromList summands)

newLPEModel :: ([TxsDefs.ChanId], [(VarId.VarId, TxsDefs.VExpr)], [LPESummand]) -> LPEModel
newLPEModel contents = (TxsDefs.empty, TxsDefs.ModelDef [] [] [] BehExprDefs.stop, newLPEProcess contents)


