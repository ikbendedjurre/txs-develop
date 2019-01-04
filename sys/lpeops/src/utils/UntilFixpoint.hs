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
untilFixpoint
) where

untilFixpoint :: Eq t => (t -> t) -> t -> t
untilFixpoint f value =
    let newValue = f value in
      if newValue /= value
      then untilFixpoint f newValue
      else value
-- untilFixpoint
