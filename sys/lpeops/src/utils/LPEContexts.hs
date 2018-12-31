{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEContexts
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEContexts (
LPEContext,
getContextFromIds,
getAbbrevContextFromIds,
getModelContext,
getProcessContext,
getSummandContext,
getValExprContext,
getAbbrevModelContext,
getAbbrevProcessContext,
getAbbrevSummandContext,
getAbbrevValExprContext
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified TxsDefs
import           LPETypeDefs
import           LPEContextIds

type LPEContext = Map.Map TxsDefs.Ident String

getContextFromIds :: Set.Set TxsDefs.Ident -> LPEContext
getContextFromIds = Map.fromSet (Text.unpack . TxsDefs.name)

getAbbrevContextFromIds :: Set.Set TxsDefs.Ident -> LPEContext
getAbbrevContextFromIds ids =
    Map.mapWithKey abbrevName (Map.fromList (zip (Set.toList ids) [1..]))
  where
    abbrevName :: TxsDefs.Ident -> Int -> String
    abbrevName j@(TxsDefs.IdSort _) i   = "Sort" ++ show i ++ "_" ++ Text.unpack (TxsDefs.name j) -- Must be capitalized!
    abbrevName j@(TxsDefs.IdCstr _) i   = "Cstr" ++ show i ++ "_" ++ Text.unpack (TxsDefs.name j) -- Must be capitalized!
    abbrevName j@(TxsDefs.IdFunc _) i   = "f" ++ show i ++ "_" ++ Text.unpack (TxsDefs.name j)
    abbrevName (TxsDefs.IdProc _) i   = "proc" ++ show i
    abbrevName (TxsDefs.IdChan _) i   = "Chan" ++ show i -- Must be capitalized!
    abbrevName (TxsDefs.IdVar _) i    = "v" ++ show i
    abbrevName (TxsDefs.IdStat _) i   = "Stat" ++ show i
    abbrevName (TxsDefs.IdModel _) i  = "Model" ++ show i
    abbrevName (TxsDefs.IdPurp _) i   = "Purp" ++ show i
    abbrevName (TxsDefs.IdGoal _) i   = "Goal" ++ show i
    abbrevName (TxsDefs.IdMapper _) i = "Mapper" ++ show i
    abbrevName (TxsDefs.IdCnect _) i  = "Cnect" ++ show i
-- getAbbrevContextFromIds

getModelContext :: LPEModel -> LPEContext
getModelContext = getContextFromIds . getModelIds

getProcessContext :: LPEProcess -> LPEContext
getProcessContext = getContextFromIds . getProcessIds

getSummandContext :: LPESummand -> LPEContext
getSummandContext = getContextFromIds . getSummandIds

getValExprContext :: TxsDefs.VExpr -> LPEContext
getValExprContext = getContextFromIds . getValExprIds

getAbbrevModelContext :: LPEModel -> LPEContext
getAbbrevModelContext = getAbbrevContextFromIds . getModelIds

getAbbrevProcessContext :: LPEProcess -> LPEContext
getAbbrevProcessContext = getAbbrevContextFromIds . getProcessIds

getAbbrevSummandContext :: LPESummand -> LPEContext
getAbbrevSummandContext = getAbbrevContextFromIds . getSummandIds

getAbbrevValExprContext :: TxsDefs.VExpr -> LPEContext
getAbbrevValExprContext = getAbbrevContextFromIds . getValExprIds





