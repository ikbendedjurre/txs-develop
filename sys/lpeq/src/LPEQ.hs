{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEQ
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEQ (
lpeqModelDef,
lpeq,
module LPEQAdmin
) where

-- import qualified Data.List as List
import qualified Data.Map as Map
-- import qualified Data.Maybe as Maybe
import qualified Control.Monad.State as MonadState
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified EnvCore as IOC
-- import qualified EnvData
import qualified TxsDefs
import LPEQAdmin
import ModelIdFactory

lpeqModelDef :: TxsDefs.ModelId -> TxsDefs.ModelDef -> String -> IOC.IOC (Either [String] (TxsDefs.ModelId, TxsDefs.ModelDef))
lpeqModelDef _modelId (TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr) outputModelName = do
    let adminData = AdminData { inChans = Set.fromList (concatMap Set.toList insyncs)
                              , outChans = Set.fromList (concatMap Set.toList outsyncs)
                              , newProcs = Map.empty
                              , finished = Map.empty
                              , queued = Set.empty
                              }
    r <- lpeq adminData bexpr
    case r of
      (Left msgs, _newAdminData) -> return (Left msgs)
      (Right newBExpr, _newAdminData) -> do tdefs' <- MonadState.gets (IOC.tdefs . IOC.state)
                                            newModelId <- getModelIdFromName (Text.pack ("LPEQ_" ++ outputModelName))
                                            let newModelDef = TxsDefs.ModelDef insyncs outsyncs splsyncs newBExpr
                                            let tdefs'' = tdefs' { TxsDefs.modelDefs = Map.insert newModelId newModelDef (TxsDefs.modelDefs tdefs') }
                                            IOC.modifyCS (\st -> st { IOC.tdefs = tdefs'' })
                                            return (Right (newModelId, newModelDef))
-- lpeqModelDef

lpeq :: AdminData -> TxsDefs.BExpr -> IOC.IOC (Either [String] TxsDefs.BExpr, AdminData)
lpeq adminData targetProc = do
    return (Right targetProc, adminData)
-- lpeq

