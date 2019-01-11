{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  UntilFixpoint
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module UntilFixpoint (
untilFixpoint,
untilFixpointM,
untilCounterOrFixpoint,
untilCounterOrFixpointM
) where

untilFixpoint :: Eq t => (t -> t) -> t -> t
untilFixpoint f value =
    let newValue = f value in
      if newValue /= value
      then untilFixpoint f newValue
      else value
-- untilFixpoint

untilFixpointM :: (Monad m, Eq t) => (t -> m t) -> t -> m t
untilFixpointM f value = do
    newValue <- f value
    if newValue /= value
    then untilFixpointM f newValue
    else return value
-- untilFixpointM

untilCounterOrFixpoint :: Eq t => Int -> (t -> t) -> t -> t
untilCounterOrFixpoint n f value =
    if n > 0
    then let newValue = f value in
           if newValue /= value
           then untilCounterOrFixpoint (n - 1) f newValue
           else value
    else value
-- untilCounterOrFixpoint

untilCounterOrFixpointM :: (Monad m, Eq t) => Int -> (t -> m t) -> t -> m t
untilCounterOrFixpointM n f value =
    if n > 0
    then do newValue <- f value
            if newValue /= value
            then untilCounterOrFixpointM (n - 1) f newValue
            else return value
    else return value
-- untilCounterOrFixpointM

