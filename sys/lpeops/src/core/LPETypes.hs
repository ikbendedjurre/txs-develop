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
lpeChanParams,
emptyLPE,
lpeParams,
LPESummands,
LPESummand(..),
lpeSmdVarSet,
lpeSmdParams,
emptyLPESummand,
LPEParamEqs,
LPEOperation,
paramEqsLookup,
selfLoopParamEqs,
defaultValueParamEqs,
newLPESummand,
newLPE
) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified TxsDefs
import qualified ChanId
import qualified VarId
import qualified ValExpr
import qualified Constant
import ValFactory
import LPEChanMap

data LPE = LPE { -- [optional] Definitions that surrounded the original TorXakis model:
                 lpeContext :: TxsDefs.TxsDefs
                 -- Multi-channels and channels with different hidden variables are mapped to fresh channels.
                 -- This map keeps a record of this transformation:
               , lpeChanMap :: LPEChanMap
                 -- [optional] Which (fresh) channels are input channels?
               , lpeInChans :: Set.Set TxsDefs.ChanId
                 -- [optional] Which (fresh) channels are output channels?
               , lpeOutChans :: Set.Set TxsDefs.ChanId
                 -- Name of the LPE process:
               , lpeName :: Text.Text
                 -- Data that the LPE process uses as parameters in its signature:
               , lpeInitEqs :: LPEParamEqs
                 -- Summands that form the body of the LPE process:
               , lpeSummands :: LPESummands
               } deriving (Eq, Ord, Show)
-- LPE

lpeChanParams :: LPE -> Set.Set TxsDefs.ChanId
lpeChanParams lpe = Set.union (lpeInChans lpe) (lpeOutChans lpe)

emptyLPE :: LPE
emptyLPE = LPE { lpeContext = TxsDefs.empty
               , lpeChanMap = Map.empty
               , lpeInChans = Set.empty
               , lpeOutChans = Set.empty
               , lpeName = Text.pack ""
               , lpeInitEqs = Map.empty
               , lpeSummands = Set.empty
               }
-- emptyLPE

lpeParams :: LPE -> Set.Set VarId.VarId
lpeParams = Map.keysSet . lpeInitEqs

type LPESummands = Set.Set LPESummand

data LPESummand = LPESummand { -- Communication channel:
                               lpeSmdChan :: TxsDefs.ChanId
                               -- Communication variables:
                             , lpeSmdVars :: [VarId.VarId]
                               -- Guard:
                             , lpeSmdGuard :: TxsDefs.VExpr
                               -- Values per parameter for the process instantiation:
                             , lpeSmdEqs :: LPEParamEqs
                             , lpeSmdDebug :: String
                             } deriving (Eq, Ord, Show)
-- LPESummand

lpeSmdParams :: LPESummand -> Set.Set VarId.VarId
lpeSmdParams = Map.keysSet . lpeSmdEqs

lpeSmdVarSet :: LPESummand -> Set.Set VarId.VarId
lpeSmdVarSet = Set.fromList . lpeSmdVars

emptyLPESummand :: LPESummand
emptyLPESummand = LPESummand { lpeSmdChan = TxsDefs.chanIdIstep
                             , lpeSmdVars = []
                             , lpeSmdGuard = ValExpr.cstrConst (Constant.Cbool True)
                             , lpeSmdEqs = Map.empty
                             , lpeSmdDebug = ""
                             }
-- emptyLPESummand

-- Relates parameters with their (initial) value:
type LPEParamEqs = Map.Map VarId.VarId TxsDefs.VExpr

-- An LPE operation takes:
--  - An input LPE;
--  - An output name (for a file or a new model);
--  - An invariant (using 'True' should have no effect);
-- An LPE operation yields either
--  - A list of (error) messages, in case there was a problem or some other event happened; or
--  - A new LPE.
type LPEOperation = LPE -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] LPE)

paramEqsLookup :: [VarId.VarId] -> LPEParamEqs -> [TxsDefs.VExpr]
paramEqsLookup orderedParams paramEqs = map fromEqs orderedParams
  where
    fromEqs :: VarId.VarId -> TxsDefs.VExpr
    fromEqs p = case paramEqs Map.!? p of
                  Just e -> e
                  Nothing -> error ("Could not find parameter \"" ++ Text.unpack (VarId.name p) ++ "\" in \"{" ++ List.intercalate ", " (map (Text.unpack . VarId.name) (Map.keys paramEqs)) ++ "}\"!")
-- paramEqsLookup

selfLoopParamEqs :: Set.Set VarId.VarId -> LPEParamEqs
selfLoopParamEqs = Map.fromSet ValExpr.cstrVar

defaultValueParamEqs :: TxsDefs.TxsDefs -> Set.Set VarId.VarId -> LPEParamEqs
defaultValueParamEqs tdefs = Map.fromSet (sort2defaultValue tdefs . VarId.varsort)

-- This method is used by unit tests:
newLPESummand :: ChanId.ChanId -> [VarId.VarId] -> TxsDefs.VExpr -> [(VarId.VarId, TxsDefs.VExpr)] -> LPESummand
newLPESummand chanId chanVars guard procInstParamEqs =
    LPESummand { lpeSmdChan = chanId
               , lpeSmdVars = chanVars
               , lpeSmdGuard = guard
               , lpeSmdEqs = Map.fromList procInstParamEqs
               , lpeSmdDebug = ""
               }
-- newLPESummand

-- This method is used by unit tests:
newLPE :: ([TxsDefs.ChanId], [(VarId.VarId, TxsDefs.VExpr)], [LPESummand]) -> LPE
newLPE (chanIds, initParamEqs, summands) =
    LPE { lpeContext = TxsDefs.empty
        , lpeChanMap = Map.fromList (map (\x -> (x, ([x], ChanId.chansorts x))) chanIds)
        , lpeInChans = Set.empty
        , lpeOutChans = Set.fromList chanIds
        , lpeName = Text.pack "LPE"
        , lpeInitEqs = Map.fromList initParamEqs
        , lpeSummands = Set.fromList summands
        }
-- newLPEProcess

