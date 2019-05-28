{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Pairs
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module Pairs (
mapPairs,
mapPairsM
) where

import qualified Control.Monad as Monad

mapPairs :: (a -> b -> c) -> [a] -> [b] -> [c]
mapPairs f xs ys = iter xs ys
  where
    iter [] _ = []
    iter (_:us) [] = iter us ys
    iter (u:us) (v:vs) = f u v : iter (u:us) vs
-- mapPairs

mapPairsM :: Monad.Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
mapPairsM f xs ys = iter xs ys
  where
    iter [] _ = return []
    iter (_:us) [] = iter us ys
    iter (u:us) (v:vs) = do
        newElem <- f u v
        otherElems <- iter (u:us) vs
        return (newElem : otherElems)
-- mapPairsM

