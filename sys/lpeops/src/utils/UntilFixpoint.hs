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
untilFixpointM
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

