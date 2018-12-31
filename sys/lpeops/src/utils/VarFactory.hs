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
createFreshIntVar,
createFreshIntVarFromPrefix
) where

import qualified EnvCore as IOC
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Data.Maybe as Maybe
import qualified SortId
import qualified SortOf
import qualified Id
import StdTDefs (stdSortTable)
import VarId

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
createFreshIntVar = createFreshVar (getStdSort "Int")

createFreshIntVarFromPrefix :: String -> IOC.IOC VarId.VarId
createFreshIntVarFromPrefix prefix = createFreshVarFromPrefix prefix (getStdSort "Int")

getStdSort :: String -> SortId.SortId
getStdSort sortName = Maybe.fromMaybe (error ("Could not find standard sort " ++ sortName ++ "!")) (Map.lookup (Text.pack sortName) stdSortTable)

