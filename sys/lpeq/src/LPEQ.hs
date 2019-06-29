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

import UniqueObjects
import ExclamToQuest
import VEnvElim
import FlattenedChannels
import PBranchInst
import ProcDepTree
import SeqProgramCounters
-- import PrefixResolution
import ProcSearch
-- import PBranchLinearization

-- Linearizes a model definition and (if successful) saves it to the current context.
lpeq :: TxsDefs.ModelId -> TxsDefs.ModelDef -> String -> IOC.IOC (Either [String] (TxsDefs.ModelId, TxsDefs.ModelDef))
lpeq _modelId (TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr) outputModelName = do
    -- TODO Keep a list of all processes that currently exist, so that
    --      temporary processes can be deleted later when done
    
    -- 1. Create copies of all involved processes (we do not want to affect the original ones):
    bexpr1 <- ensureFreshProcsInBExpr bexpr
    -- IOC.putInfo [ "BEXPR1::" ]
    -- printProcsInBExpr bexpr1
    
    -- 2. Convert !x to ?x:
    bexpr2 <- exclamToQuest bexpr1
    -- IOC.putInfo [ "BEXPR2::" ]
    -- printProcsInBExpr bexpr2
    
    -- 3. Eliminate variable environments through substitution:
    bexpr3 <- eliminateVEnvs bexpr2
    -- IOC.putInfo [ "BEXPR3::" ]
    -- printProcsInBExpr bexpr3
    
    -- TODO Eliminate StAuts
    
    -- 5. Create process instantiations for branches with parallel structures (Parallel, Enable, Disable, Interrupt):
    let allChanIds = concatMap Set.toList (insyncs ++ outsyncs)
    bexpr4 <- doPBranchInst allChanIds bexpr3
    -- IOC.putInfo [ "BEXPR4::" ]
    -- printProcsInBExpr bexpr4
    
    -- 6. Create processes for each instantiation where the channels are different.
    --    This makes the channel-related part of process signature redundant.
    bexpr5 <- flattenChannels allChanIds bexpr4
    -- IOC.putInfo [ "BEXPR5::" ]
    -- printProcsInBExpr bexpr5
    
    -- Before continuing, validate the process dependency tree.
    -- This must (at least) happen AFTER doPBranchInst (since process instantiations are used to check for recurring visits)!
    problems <- getProcDepTreeProblems bexpr5
    if null problems
    then do 
            -- IOC.putInfo [ "BEXPR5::" ]
            -- printProcsInBExpr bexpr5
            
            bexpr6 <- ensureFreshVarsInBExpr bexpr5
            IOC.putInfo [ "BEXPR6::" ]
            printProcsInBExpr bexpr6
            
            -- 7. Place all steps of a process (including steps inside instantiated processes) on the same level in a Choice expression, but
            --    with different requirements of the value of a program counter.
            --    Each member of the Choice expression is called a 'branch' (and could become a summand later).
            --    Exception: branches with parallel structures are not visited internally!
            
            bexpr7 <- addSeqProgramCounters bexpr6
            IOC.putInfo [ "BEXPR7::" ]
            printProcsInBExpr bexpr7
            
            -- 8. Rewrite the branches of the involved processes so that they have a single ActOffer.
            --    Exception: branches with parallel structures are not rewritten here!
            -- bexpr8 <- resolvePrefixes bexpr7
            -- printProcsInBExpr bexpr8
            
            -- 9. Linearize branches with parallel structures:
            --_bexpr9 <- linearizePBranches bexpr8
            -- printProcsInBExpr bexpr9
            
            -- Save the result as a new model:
            tdefs' <- MonadState.gets (IOC.tdefs . IOC.state)
            newModelId <- getModelIdFromName (Text.pack ("LPEQ_" ++ outputModelName))
            let newModelDef = TxsDefs.ModelDef insyncs outsyncs splsyncs bexpr7
            let tdefs'' = tdefs' { TxsDefs.modelDefs = Map.insert newModelId newModelDef (TxsDefs.modelDefs tdefs') }
            IOC.modifyCS (\st -> st { IOC.tdefs = tdefs'' })
            return (Right (newModelId, newModelDef))
    else return (Left problems)
-- lpeqModelDef













