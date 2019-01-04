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
printLPE,
exportLPE,
module LPETypes
) where

import qualified Control.Monad.State as MonadState
import qualified Data.Text as Text
import qualified EnvCore as IOC
import qualified EnvData
import qualified TxsDefs
import           LPEPrettyPrint
import           LPEConversion
import           LPEValidity
import           LPETypes

lpeOpsVersion :: String
lpeOpsVersion = "2019.01.04.08"

data LPEOp = LPEOpLoop | LPEOp LPEOperation

-- An LPE operation takes:
--  - An input LPE;
--  - An output name (for a file or a new model);
--  - An invariant (using 'True' should have no effect);
-- An LPE operation yields either
--  - A list of (error) messages, in case there was a problem or some other event happened; or
--  - A new LPE.
type LPEOperation = LPE -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] LPE)

-- Core method that does the following:
--  1. Transforms a closed process expression to an LPE;
--  2. Applies the given operations to the LPE, which results in a new LPE;
--  3. Transforms the new LPE to a new model (with the specified name) and process.
lpeOperations :: [LPEOp] -> TxsDefs.ModelId -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] TxsDefs.ModelId)
lpeOperations operations modelId out invariant = do
    msgsOrLpe <- model2lpe modelId
    case msgsOrLpe of
      Left msgs -> return (Left msgs)
      Right lpe -> do msgsOrNewLpe <- lpeOperation operations operations [lpe, lpe] out invariant
                      case msgsOrNewLpe of
                        Left msgs -> return (Left msgs)
                        Right [] -> return (Left ["No output LPE found!"]) -- Should not happen.
                        Right (newLpe:_) -> do if newLpe /= lpe
                                               then IOC.putMsgs [ EnvData.TXS_CORE_ANY "LPE has been rewritten!" ]
                                               else IOC.putMsgs [ EnvData.TXS_CORE_ANY "LPE is identical to input!" ]
                                               temp <- lpe2model (newLpe { lpeName = Text.pack out })
                                               return (Right temp)
-- lpeOperations

lpeOperation :: [LPEOp] -> [LPEOp] -> [LPE] -> String -> TxsDefs.VExpr -> IOC.IOC (Either [String] [LPE])
lpeOperation _ops _ [] _out _invariant = return (Left ["No input LPE found!"])
lpeOperation _ops [] lpeInstances _out _invariant = return (Right lpeInstances)
lpeOperation ops (LPEOpLoop:xs) (lpe:ys) out invariant =
    if lpe `elem` ys
    then lpeOperation ops xs (lpe:ys) out invariant
    else lpeOperation ops ops (lpe:lpe:ys) out invariant
lpeOperation ops (LPEOp op:xs) (lpe:ys) out invariant = do
    msgsOrNewLpe <- op lpe out invariant
    case msgsOrNewLpe of
      Left msgs -> return (Left msgs)
      Right newLpe -> let problems = validateLPE newLpe in
                        if null problems
                        then lpeOperation ops xs (newLpe:ys) out invariant
                        else return (Left problems)
-- lpeOperation

discardLPE :: LPEOperation
discardLPE _ _ _ = return (Left ["LPE discarded!"])

printLPE :: LPEOperation
printLPE lpe _out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY (showAbbrevLPE lpe) ]
    return (Right lpe)
-- printLPE

exportLPE :: LPEOperation
exportLPE lpe out _invariant = do
    IOC.putMsgs [ EnvData.TXS_CORE_ANY "<<export>>" ]
    let filename = out ++ ".txs"
    MonadState.liftIO $ writeFile filename (showAbbrevLPE lpe)
    return (Left ["LPE exported to " ++ filename ++ "!"])
-- exportLPE

