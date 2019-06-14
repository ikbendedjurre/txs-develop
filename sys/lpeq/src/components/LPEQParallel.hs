{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  LPEQParallel
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE ViewPatterns        #-}

module LPEQParallel (
lpeqParallel
) where

import qualified EnvCore as IOC
import qualified ProcId
import qualified ProcDef

import LPEQComp

lpeqParallel :: LPEQCompFunc
lpeqParallel parentPid children = do
    
-- lpeqParallel

