{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  VarFactory
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module VarFactory (
createFreshVar,
createFreshVarFromVar,
createFreshVarFromPrefix,
createFreshVars,
createFreshIntVar,
createFreshIntVarFromPrefix,
createFreshBoolVar,
createFreshBoolVarFromPrefix
) where

import qualified Control.Monad as Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified SortId
import qualified SortOf
import qualified Id
import VarId
import SortFactory

createFreshVars :: Set.Set VarId.VarId -> IOC.IOC (Map.Map VarId.VarId VarId.VarId)
createFreshVars vids = Map.fromList <$> Monad.mapM createFreshVarPair (Set.toList vids)
  where
    createFreshVarPair :: VarId.VarId -> IOC.IOC (VarId.VarId, VarId.VarId)
    createFreshVarPair varId = do
        newVarId <- createFreshVarFromVar varId
        return (varId, newVarId)
-- createFreshVars

-- Creates a variable of the specified sort, using the specified string as part of the name.
createFreshVar :: SortId.SortId -> IOC.IOC VarId.VarId
createFreshVar = createFreshVarFromPrefix "__FV"

-- Creates a variable of the specified sort, using the specified string as part of the name.
createFreshVarFromPrefix :: String -> SortId.SortId -> IOC.IOC VarId.VarId
createFreshVarFromPrefix prefix sort = do
    varUnid <- IOC.newUnid
    let idAsInt = Id._id varUnid
    let absId = if idAsInt >= 0 then idAsInt else -idAsInt
    return VarId.VarId { VarId.name = Text.pack (prefix ++ show absId), VarId.unid = varUnid, VarId.varsort = sort }
-- createFreshVarFromPrefix

createFreshVarFromVar :: VarId -> IOC.IOC VarId.VarId
createFreshVarFromVar varId = createFreshVarFromPrefix (Text.unpack (name varId)) (SortOf.sortOf varId)

createFreshIntVar :: IOC.IOC VarId.VarId
createFreshIntVar = createFreshVar getIntSort

createFreshIntVarFromPrefix :: String -> IOC.IOC VarId.VarId
createFreshIntVarFromPrefix prefix = createFreshVarFromPrefix prefix getIntSort

createFreshBoolVar :: IOC.IOC VarId.VarId
createFreshBoolVar = createFreshVar getBoolSort

createFreshBoolVarFromPrefix :: String -> IOC.IOC VarId.VarId
createFreshBoolVarFromPrefix prefix = createFreshVarFromPrefix prefix getBoolSort

