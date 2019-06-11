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
lpeq
) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
-- import qualified EnvData
import qualified TxsDefs
import ModelIdFactory

import ProcCopy
import ExclamToQuest
import VEnvElim
import PBranchInst
import ProcDepTree
import ProgramCounters

-- Linearizes a model definition and (if successful) saves it to the current context.
lpeq :: TxsDefs.ModelId -> TxsDefs.ModelDef -> String -> IOC.IOC (Either [String] (TxsDefs.ModelId, TxsDefs.ModelDef))
lpeq _modelId (TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr) outputModelName = do
    -- 1. Create copies of all processes (we do not want to affect existing processes):
    bexpr' <- replaceProcsInBExpr bexpr
    -- 2. Convert !x to ?x:
    bexpr'' <- exclamToQuest bexpr'
    -- Eliminate variable environments through substitution:
    bexpr''' <- eliminateVEnvs bexpr''
    -- 3. Create process instantiations for parallel branches:
    let cids = concatMap Set.toList (insyncs ++ outsyncs)
    msgsOrInst <- doPBranchInst (Set.fromList cids) bexpr'''
    case msgsOrInst of
      Left msgs -> return (Left msgs)
      Right inst -> do -- 4. Add program counters to the signatures of processes:
                       inst' <- addProgramCounters inst
                       -- 5. 
                       msgsOrTree <- getProcDepTree inst'
                       case msgsOrTree of
                         Left msgs -> return (Left msgs)
                         Right _procInstTree -> do tdefs' <- MonadState.gets (IOC.tdefs . IOC.state)
                                                   newModelId <- getModelIdFromName (Text.pack ("LPEQ_" ++ outputModelName))
                                                   let newModelDef = TxsDefs.ModelDef insyncs outsyncs splsyncs inst
                                                   let tdefs'' = tdefs' { TxsDefs.modelDefs = Map.insert newModelId newModelDef (TxsDefs.modelDefs tdefs') }
                                                   IOC.modifyCS (\st -> st { IOC.tdefs = tdefs'' })
                                                   return (Right (newModelId, newModelDef))
-- lpeqModelDef













