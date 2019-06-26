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
import SeqProgramCounters
import PrefixResolution
import ProcSearch
import PBranchLinearization

-- Linearizes a model definition and (if successful) saves it to the current context.
lpeq :: TxsDefs.ModelId -> TxsDefs.ModelDef -> String -> IOC.IOC (Either [String] (TxsDefs.ModelId, TxsDefs.ModelDef))
lpeq _modelId (TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr) outputModelName = do
    -- TODO Keep a list of all processes that currently exist, so that
    --      temporary processes can be deleted later when done
    
    -- 1. Create copies of all processes (we do not want to affect existing processes):
    bexpr1 <- replaceProcsInBExpr bexpr
    
    -- 2. Convert !x to ?x:
    bexpr2 <- exclamToQuest bexpr1
    
    -- 3. Eliminate variable environments through substitution:
    bexpr3 <- eliminateVEnvs bexpr2
    
    -- TODO Eliminate StAuts
    
    -- 4. Create process instantiations for parallel branches:
    let allChanIds = concatMap Set.toList (insyncs ++ outsyncs)
    bexpr4 <- doPBranchInst allChanIds bexpr3
    
    -- 5. Flatten channels (so that channel-related part of process signature becomes redundant):
    bexpr5 <- flattenChannels allChanIds bexpr4
    
    -- Before continuing, validate the process dependency tree.
    -- This must (at least) happen AFTER doPBranchInst!
    problems <- getProcDepTreeProblems bexpr5
    if null problems
    then do -- 6. Add program counters to all involved processes:
            bexpr6 <- addSeqProgramCounters bexpr5
            -- printProcsInBExpr bexpr6
            
            -- 8. Rewrite processes so that they consist of summands and structures with parallel branches, exclusively:
            bexpr7 <- resolvePrefixes bexpr6
            -- printProcsInBExpr bexpr7
            
            -- 9. Linearize structures with parallel branches:
            bexpr8 <- linearizePBranches bexpr7
            printProcsInBExpr bexpr8 -- Bla bla.
            
            -- Save the result as a new model:
            tdefs' <- MonadState.gets (IOC.tdefs . IOC.state)
            newModelId <- getModelIdFromName (Text.pack ("LPEQ_" ++ outputModelName))
            let newModelDef = TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr8
            let tdefs'' = tdefs' { TxsDefs.modelDefs = Map.insert newModelId newModelDef (TxsDefs.modelDefs tdefs') }
            IOC.modifyCS (\st -> st { IOC.tdefs = tdefs'' })
            return (Right (newModelId, newModelDef))
    else return (Left problems)
-- lpeqModelDef













