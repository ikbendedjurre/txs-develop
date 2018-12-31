{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ModelIdFactory
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module ModelIdFactory (
getModelsByName,
getModelIdFromName,
getEitherModelFromName
) where

import qualified Control.Monad.State as MonadState
import qualified EnvCore as IOC
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified ModelId
import qualified TxsDefs

-- Gets all models with a given name:
getModelsByName :: String -> IOC.IOC (Map.Map ModelId.ModelId TxsDefs.ModelDef)
getModelsByName modelName = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } ->
        return (Map.filterWithKey (\(TxsDefs.ModelId n _) _ -> Text.unpack n == modelName) (TxsDefs.modelDefs tdefs))
      _ -> return Map.empty
-- getModelsByName

-- Gets the id of an existing model, or creates the id for a new model:
getModelIdFromName :: String -> IOC.IOC ModelId.ModelId
getModelIdFromName modelName = do
    matchingModels <- getModelsByName modelName
    case Map.toList matchingModels of
      [] -> TxsDefs.ModelId (Text.pack modelName) <$> IOC.newUnid
      (mid, _):_ -> return mid
-- getModelIdFromName

-- Gets the id and definition of an existing model, or
-- produces a message describing which model names would have been valid:
getEitherModelFromName :: String -> IOC.IOC (Either String (ModelId.ModelId, TxsDefs.ModelDef))
getEitherModelFromName modelName = do
    envc <- MonadState.get
    case IOC.state envc of
      IOC.Initing { IOC.tdefs = tdefs } ->
        do let modelDefs = TxsDefs.modelDefs tdefs
           let matchingModels = Map.filterWithKey (\(TxsDefs.ModelId n _) _ -> Text.unpack n == modelName) modelDefs
           if matchingModels == Map.empty
           then return (Left ("Expected " ++ List.intercalate " or " (map (Text.unpack . ModelId.name) (Map.keys modelDefs)) ++ ", found " ++ modelName ++ "!"))
           else return (Right (Map.toList matchingModels !! 0))
      _ -> return (Left "TorXakis core is not initialized!")
-- getEitherModelFromName



