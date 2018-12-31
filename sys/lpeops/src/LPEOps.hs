{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEOps
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module LPEOps (
lpeOpsVersion,
LPEOp(..),
LPEOperation,
lpeOperations,
discardLPE,
showLPE,
exportLPE,
module LPETypes
) where

import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import           LPETypes
import           LPEPrettyPrint

lpeOpsVersion :: String
lpeOpsVersion = "0.13.1"

data LPEOp = LPEOpLoop | LPEOp LPEOperation

-- An LPE operation takes:
--  - An input LPE;
--  - An output name (for a file or a new model);
--  - An invariant (using 'True' should have no effect);
-- An LPE operation yields either
--  - A list of (error) messages, in case there was a problem or some other event happened; or
--  - A new LPE instance.
type LPEOperation = LPEModel -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] LPEModel)

-- Core method that does the following:
--  1. Transforms a closed process expression to an LPE instance;
--  2. Applies the given operation to the LPE instance, which results in a new LPE instance;
--  3. Transforms the new LPE instance to a process definition with the specified name and
--     a process expression that creates an instance of this process definition.
lpeOperations :: [LPEOp] -> TxsDefs.ModelDef -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] (TxsDefs.BExpr, TxsDefs.ProcId, TxsDefs.ProcDef))
lpeOperations operations modelDef out invariant = do
    eitherModel <- toLPEModel modelDef
    case eitherModel of
      Left msgs -> return (Left msgs)
      Right model -> do eitherNewModel <- lpeOperation operations operations [model, model] out invariant
                        case eitherNewModel of
                          Left msgs -> return (Left msgs)
                          Right [] -> return (Left ["No output LPE found!"])
                          Right (newModel:_) -> do if newModel /= model
                                                   then IOC.putMsgs [ EnvData.TXS_CORE_ANY "LPE instance has been rewritten!" ]
                                                   else IOC.putMsgs [ EnvData.TXS_CORE_ANY "LPE instance is identical to input!" ]
                                                   temp <- fromLPEModel newModel out
                                                   return (Right temp)
-- lpeOperations

lpeOperation :: [LPEOp] -> [LPEOp] -> [LPEModel] -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] [LPEModel])
lpeOperation _ops _ [] _out _invariant = return (Left ["No input LPE found!"])
lpeOperation _ops [] lpeInstances _out _invariant = return (Right lpeInstances)
lpeOperation ops (LPEOpLoop:xs) (model:ys) out invariant =
    if model `elem` ys
    then lpeOperation ops xs (model:ys) out invariant
    else lpeOperation ops ops (model:model:ys) out invariant
lpeOperation ops (LPEOp op:xs) (model:ys) out invariant = do
    eitherNewModel <- op model out invariant
    case eitherNewModel of
      Left msgs -> return (Left msgs)
      Right newModel@(_, _, x) -> let problems = getProcessProblems x in
                                    if null problems
                                    then lpeOperation ops xs (newModel:ys) out invariant
                                    else return (Left problems)
-- lpeOperation

discardLPE :: LPEOperation
discardLPE _ _ _ = return (Left ["LPE discarded!"])

showLPE :: LPEOperation
showLPE model _out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY (showAbbrevLPEModel model) ]
    return (Right model)
-- showLPE

exportLPE :: LPEOperation
exportLPE model out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<export>>" ]
    let filename = out ++ ".txs"
    MonadState.liftIO $ writeFile filename (showAbbrevLPEModel model)
    return (Left ["Model exported to " ++ filename ++ "!"])
-- exportLPE

