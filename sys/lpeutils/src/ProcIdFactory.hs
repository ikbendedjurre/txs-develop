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
getProcsByName,
-- getProcIdFromName,
getMsgOrProcFromName
) where

import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified ProcId
import qualified TxsDefs

-- Gets all processes with a given name:
getProcsByName :: Text.Text -> IOC.IOC (Map.Map ProcId.ProcId TxsDefs.ProcDef)
getProcsByName procName = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } ->
        return (Map.filterWithKey (\(TxsDefs.ProcId n _ _ _ _) _ -> n == procName) (TxsDefs.procDefs tdefs))
      _ -> return Map.empty
-- getProcsByName

-- -- Gets the id of an existing process, or creates the id for a new process:
-- getProcIdFromName :: Text.Text -> IOC.IOC ProcId.ProcId
-- getProcIdFromName procName = do
    -- matchingProcs <- getProcsByName procName
    -- case Map.toList matchingProcs of
      -- [] -> TxsDefs.ProcId procName <$> IOC.newUnid
      -- (pid, _):_ -> return pid
-- -- getProcIdFromName

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



