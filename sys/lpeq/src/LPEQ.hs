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

{-# LANGUAGE ViewPatterns        #-}

module LPEQ (
lpeqModelDef,
lpeqBExpr
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
import qualified ProcId
import qualified LPEQAdmin
import ModelIdFactory
import ProcIdFactory
import BehExprDefs

-- Linearizes a model definition and (if successful) saves it to the current context.
lpeqModelDef :: TxsDefs.ModelId -> TxsDefs.ModelDef -> String -> IOC.IOC (Either [String] (TxsDefs.ModelId, TxsDefs.ModelDef))
lpeqModelDef _modelId (TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr) outputModelName = do
    let adminData = LPEQAdmin.AdminData { LPEQAdmin.inChans = Set.fromList (concatMap Set.toList insyncs)
                                        , LPEQAdmin.outChans = Set.fromList (concatMap Set.toList outsyncs)
                                        , LPEQAdmin.newProcs = Map.empty
                                        , LPEQAdmin.finished = Map.empty
                                        , LPEQAdmin.queued = Set.empty
                                        , LPEQAdmin.failed = Set.empty
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

-- Linearizes a behavioral expression.
-- However, it first checks whether the linearization of the expression
--  - is not already in progress (infinite loop);
--  - was attempted before and failed;
--  - was done before and can simply be reused.
lpeqBExpr :: LPEQAdmin.AdminData -> TxsDefs.BExpr -> IOC.IOC (Either [String] TxsDefs.BExpr, LPEQAdmin.AdminData)
lpeqBExpr adminData bexpr = do
    case LPEQAdmin.finished adminData Map.!? bexpr of
      Just x -> return (Right x, adminData)
      Nothing -> if Set.member bexpr (LPEQAdmin.failed adminData)
                 then return (Left [], adminData)
                 else if Set.member bexpr (LPEQAdmin.queued adminData)
                      then return (Left ["Infinite loop detected!"], LPEQAdmin.addToFailed bexpr adminData)
                      else do r <- lpeq (LPEQAdmin.addToQueued bexpr adminData) bexpr
                              case r of
                                (Left msgs, newAdminData) -> return (Left msgs, LPEQAdmin.addToFailed bexpr newAdminData)
                                (Right newBExpr, newAdminData) -> return (Right newBExpr, LPEQAdmin.addToFinished bexpr newBExpr newAdminData)
-- lpeqBExpr

-- Linearizes a behavioral expression.
-- Does NOT perform any safety checks (like lpeqBExpr does)!
lpeq :: LPEQAdmin.AdminData -> TxsDefs.BExpr -> IOC.IOC (Either [String] TxsDefs.BExpr, LPEQAdmin.AdminData)
lpeq adminData bexpr = do
    case bexpr of
      (TxsDefs.view -> ProcInst pid _cids _vexprs) ->
          do r <- getMsgOrProcFromName (ProcId.name pid)
             case r of
               Left msg -> return (Left ["Could not find instantiated process!", msg], adminData)
               Right (_, ProcDef.ProcDef _cids _vids body) -> lpeqBExpr adminData body
      (TxsDefs.view -> Guard _guard _bexpr) -> return (Left ["No implementation yet for Guard!"], adminData)
      (TxsDefs.view -> Choice _bexprs) -> return (Left ["No implementation yet for Choice!"], adminData)
      (TxsDefs.view -> Parallel _cidSet _bexprs) -> return (Left ["No implementation yet for Parallel!"], adminData)
      (TxsDefs.view -> Hide _cidSet _bexpr) -> return (Left ["No implementation yet for Hide!"], adminData)
      (TxsDefs.view -> Enable _bexpr1 _acceptOffers _bexpr2) -> return (Left ["No implementation yet for Enable!"], adminData)
      (TxsDefs.view -> Disable _bexpr1 _bexpr2) -> return (Left ["No implementation yet for Disable!"], adminData)
      (TxsDefs.view -> Interrupt _bexpr1 _bexpr2) -> return (Left ["No implementation yet for Interrupt!"], adminData)
      (TxsDefs.view -> ActionPref _offer _bexpr) -> return (Left ["No implementation yet for ActionPref!"], adminData)
      (TxsDefs.view -> ValueEnv _venv _bexpr) -> return (Left ["No implementation yet for ValueEnv!"], adminData)
      (TxsDefs.view -> StAut {}) -> return (Left ["No implementation yet for StAut!"], adminData)
      _ -> return (Left ["Behavioral expression not accounted for (\"" ++ show bexpr ++ "\")!"], adminData)
-- lpeq





















