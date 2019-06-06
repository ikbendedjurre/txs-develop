{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ProcIdFactory
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module ProcIdFactory (
createFreshProcIdFromProcId,
createFreshProcIdFromChansAndVars,
createFreshProcIdWithDifferentVars,
getProcById,
getProcsByName,
getMsgOrProcFromName
) where

import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified ProcId
import qualified ChanId
import qualified VarId
import qualified SortId
import qualified SortOf
import qualified TxsDefs

-- Creates a fresh process id based on a given process id:
createFreshProcIdFromProcId :: ProcId.ProcId -> IOC.IOC ProcId.ProcId
createFreshProcIdFromProcId pid = iter (Text.unpack (ProcId.name pid)) 1
  where
    iter :: String -> Int -> IOC.IOC ProcId.ProcId
    iter procName suffix = do
        let procNameAttempt = Text.pack (procName ++ show suffix)
        matchingProcs <- getProcsByName procNameAttempt
        if Map.null matchingProcs
        then do i <- IOC.newUnid
                return (pid { ProcId.name = procNameAttempt, ProcId.unid = i })
        else iter procName (suffix + 1)
-- getProcIdFromName

createFreshProcIdFromChansAndVars :: Text.Text -> [ChanId.ChanId] -> [VarId.VarId] -> ProcId.ExitSort -> IOC.IOC ProcId.ProcId
createFreshProcIdFromChansAndVars procName cids vids exit = do
    i <- IOC.initUnid
    createFreshProcIdFromProcId (ProcId.ProcId procName i (map ProcId.toChanSort cids) (map SortOf.sortOf vids) exit)
-- createFreshProcIdFromChansAndVars

createFreshProcIdWithDifferentVars :: ProcId.ProcId -> [SortId.SortId] -> IOC.IOC ProcId.ProcId
createFreshProcIdWithDifferentVars (ProcId.ProcId name _ cids _ exit) sids = do
    i <- IOC.initUnid
    createFreshProcIdFromProcId (ProcId.ProcId name i cids sids exit)
-- createFreshProcIdWithDifferentVars

-- Gets all processes with a given name:
getProcById :: ProcId.ProcId -> IOC.IOC (Maybe TxsDefs.ProcDef)
getProcById procId = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } ->
        return ((TxsDefs.procDefs tdefs) Map.!? procId)
      _ -> return Nothing
-- getProcById

-- Gets all processes with a given name:
getProcsByName :: Text.Text -> IOC.IOC (Map.Map ProcId.ProcId TxsDefs.ProcDef)
getProcsByName procName = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } ->
        return (Map.filterWithKey (\(TxsDefs.ProcId n _ _ _ _) _ -> n == procName) (TxsDefs.procDefs tdefs))
      _ -> return Map.empty
-- getProcsByName

-- Gets the id and definition of an existing process, or
-- produces a message describing which process names would have been valid:
getMsgOrProcFromName :: Text.Text -> IOC.IOC (Either String (ProcId.ProcId, TxsDefs.ProcDef))
getMsgOrProcFromName procName = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } ->
        do let procDefs = TxsDefs.procDefs tdefs
           let matchingProcs = Map.filterWithKey (\(TxsDefs.ProcId n _ _ _ _) _ -> n == procName) procDefs
           if matchingProcs == Map.empty
           then return (Left ("Expected " ++ List.intercalate " or " (map (Text.unpack . ProcId.name) (Map.keys procDefs)) ++ ", found " ++ Text.unpack procName ++ "!"))
           else return (Right (Map.toList matchingProcs !! 0))
      _ -> return (Left "TorXakis core is not initialized!")
-- getMsgOrProcFromName

