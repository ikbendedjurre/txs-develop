{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPETypes
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPETypes (
LPE(..),
emptyLPE,
LPESummands,
LPESummand(..),
emptyLPESummand,
LPEChanOffer,
LPEChanOffers,
LPEParamEqs,
paramEqsLookup,
newLPESummand,
newLPE
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import qualified ChanId
import qualified VarId
import qualified ValExpr
import qualified Constant

data LPE = LPE { -- [optional] Definitions that surrounded the original TorXakis model:
                 lpeContext :: TxsDefs.TxsDefs
                 -- [optional] Which (sets of) channels are input channels?
               , lpeInChans :: Set.Set (Set.Set TxsDefs.ChanId)
                 -- [optional] Which (sets of) channels are output channels?
               , lpeOutChans :: Set.Set (Set.Set TxsDefs.ChanId)
                 -- Name of the LPE process:
               , lpeName :: Text.Text
                 -- Channels that the LPE process uses as parameters in its signature:
               , lpeChanParams :: Set.Set TxsDefs.ChanId
                 -- Data that the LPE process uses as parameters in its signature:
               , lpeInitEqs :: LPEParamEqs
                 -- Summands that form the body of the LPE process:
               , lpeSummands :: LPESummands
               } deriving (Eq, Ord, Show)
-- LPE

emptyLPE :: LPE
emptyLPE = LPE { lpeContext = TxsDefs.empty
               , lpeInChans = Set.empty
               , lpeOutChans = Set.empty
               , lpeName = Text.pack ""
               , lpeChanParams = Set.empty
               , lpeInitEqs = Map.empty
               , lpeSummands = Set.empty
               }
-- emptyLPE

type LPESummands = Set.Set LPESummand

data LPESummand = LPESummand { -- All local (=channel) variables, including hidden ones, which must all be fresh:
                               lpeSmdVars :: Set.Set VarId.VarId
                               -- Channel offers (see below):
                             , lpeSmdOffers :: LPEChanOffers
                               -- Guard:
                             , lpeSmdGuard :: TxsDefs.VExpr
                               -- Values per parameter for the process instantiation:
                             , lpeSmdEqs :: LPEParamEqs
                             } deriving (Eq, Ord, Show)
-- LPESummand

emptyLPESummand :: LPESummand
emptyLPESummand = LPESummand { lpeSmdVars = Set.empty
                             , lpeSmdOffers = Map.empty
                             , lpeSmdGuard = ValExpr.cstrConst (Constant.Cbool True)
                             , lpeSmdEqs = Map.empty
                             }
-- emptyLPESummand

-- Relates channels with the communication variables over which they must be synchronized:
type LPEChanOffers = Map.Map TxsDefs.ChanId [VarId.VarId]
type LPEChanOffer = (ChanId.ChanId, [VarId.VarId])

-- Relates parameters with their (initial) value:
type LPEParamEqs = Map.Map VarId.VarId TxsDefs.VExpr

paramEqsLookup :: [VarId.VarId] -> LPEParamEqs -> [TxsDefs.VExpr]
paramEqsLookup orderedParams paramEqs = map fromEqs orderedParams
  where
    fromEqs :: VarId.VarId -> TxsDefs.VExpr
    fromEqs p = case paramEqs Map.!? p of
                  Just e -> e
                  Nothing -> error ("Could not find parameter \"" ++ Text.unpack (VarId.name p) ++ "\" in \"{" ++ List.intercalate ", " (map (Text.unpack . VarId.name) (Map.keys paramEqs)) ++ "}\"!")
-- paramEqsLookup

newLPESummand :: [VarId.VarId] -> [(ChanId.ChanId, [VarId.VarId])] -> TxsDefs.VExpr -> [(VarId.VarId, TxsDefs.VExpr)] -> LPESummand
newLPESummand chanVarIds chanOffers guard procInstParamEqs =
    LPESummand { lpeSmdVars = Set.fromList chanVarIds
               , lpeSmdOffers = Map.fromList chanOffers
               , lpeSmdGuard = guard
               , lpeSmdEqs = Map.fromList procInstParamEqs
               }
-- newLPESummand

newLPE :: ([TxsDefs.ChanId], [(VarId.VarId, TxsDefs.VExpr)], [LPESummand]) -> LPE
newLPE (chanIds, initParamEqs, summands) =
    LPE { lpeContext = TxsDefs.empty
        , lpeInChans = Set.empty
        , lpeOutChans = Set.empty
        , lpeName = Text.pack "LPE"
        , lpeChanParams = Set.fromList chanIds
        , lpeInitEqs = Map.fromList initParamEqs
        , lpeSummands = Set.fromList summands
        }
-- newLPEProcess

