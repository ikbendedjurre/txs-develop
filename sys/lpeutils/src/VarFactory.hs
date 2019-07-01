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
getUsedNames,
printUsedNameCount,
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
import qualified Control.Monad.State as MonadState
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Char as Char
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified TxsDefs as TxsDefs
import qualified SortId
import qualified SortOf
import VarId
import SortFactory

getUsedNames :: IOC.IOC (Set.Set Text.Text)
getUsedNames = TxsDefs.usedNames <$> MonadState.gets (IOC.tdefs . IOC.state)

printUsedNameCount :: String -> IOC.IOC ()
printUsedNameCount caption = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    let usedNames = TxsDefs.usedNames tdefs
    IOC.putInfo ["Used Name Count [" ++ caption ++ "] = " ++ show (Set.size usedNames)]
-- printUsedNameCount

-- Creates a variable of the specified sort, using the specified string as part of the name.
createFreshVarFromPrefix :: String -> SortId.SortId -> IOC.IOC VarId.VarId
createFreshVarFromPrefix prefix sort = do
    tdefs <- MonadState.gets (IOC.tdefs . IOC.state)
    let usedNames = TxsDefs.usedNames tdefs
    -- IOC.putInfo (map (\t -> "Name Already In Use = " ++ Text.unpack t) (Set.toList usedNames))
    let uniqueName = getUniqueName usedNames (reverse (dropWhile Char.isDigit (reverse prefix))) 1
    -- IOC.putInfo ["New Unique Name (" ++ show (Set.size usedNames) ++ ") = " ++ Text.unpack uniqueName]
    let tdefs' = tdefs { TxsDefs.usedNames = Set.insert uniqueName usedNames }
    IOC.modifyCS $ \st -> st { IOC.tdefs = tdefs' }
    varUnid <- IOC.newUnid
    return VarId.VarId { VarId.name = uniqueName, VarId.unid = varUnid, VarId.varsort = sort }
  where
    getUniqueName :: Set.Set Text.Text -> String -> Int -> Text.Text
    getUniqueName usedNames truePrefix nr =
        let attempt = Text.pack (truePrefix ++ show nr) in
          if Set.member attempt usedNames
          then getUniqueName usedNames truePrefix (nr + 1)
          else attempt
    -- getUniqueName
-- createFreshVarFromPrefix

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
createFreshVar = createFreshVarFromPrefix "fv"

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

