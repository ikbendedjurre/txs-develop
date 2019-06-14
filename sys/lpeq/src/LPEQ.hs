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
import FlattenedChannels
import PBranchInst
import ProcDepTree
import ProgramCounters
--import LPEQLinearization

-- Linearizes a model definition and (if successful) saves it to the current context.
lpeq :: TxsDefs.ModelId -> TxsDefs.ModelDef -> String -> IOC.IOC (Either [String] (TxsDefs.ModelId, TxsDefs.ModelDef))
lpeq _modelId (TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr) outputModelName = do
    -- 1. Create copies of all processes (we do not want to affect existing processes):
    bexpr1 <- replaceProcsInBExpr bexpr
    
    -- 2. Convert !x to ?x:
    bexpr2 <- exclamToQuest bexpr1
    
    -- 3. Eliminate variable environments through substitution:
    bexpr3 <- eliminateVEnvs bexpr2
    
    -- 4. Create process instantiations for parallel branches:
    let allChanIds = concatMap Set.toList (insyncs ++ outsyncs)
    bexpr4 <- doPBranchInst allChanIds bexpr3
    
    -- 5. Flatten channels (so that channel-related part of process signature becomes redundant):
    bexpr5 <- flattenChannels allChanIds bexpr4
    
    -- 6. Add program counters to the signatures of processes:
    bexpr6 <- addProgramCounters bexpr5
    
    -- 7. Compute and validate the process dependency tree:
    msgsOrTree <- getProcDepTree bexpr6
    case msgsOrTree of
      Left msgs -> return (Left msgs)
      Right _procInstTree -> do --linearize procInstTree
                                tdefs' <- MonadState.gets (IOC.tdefs . IOC.state)
                                newModelId <- getModelIdFromName (Text.pack ("LPEQ_" ++ outputModelName))
                                let newModelDef = TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr6
                                let tdefs'' = tdefs' { TxsDefs.modelDefs = Map.insert newModelId newModelDef (TxsDefs.modelDefs tdefs') }
                                IOC.modifyCS (\st -> st { IOC.tdefs = tdefs'' })
                                return (Right (newModelId, newModelDef))
-- lpeqModelDef













