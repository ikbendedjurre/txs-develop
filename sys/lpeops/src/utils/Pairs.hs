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
knuthShuffle,
allPairs,
allPairsNonId,
halfOfPairs,
halfOfPairsNonId
) where

import System.Random
import Control.Monad

-- From https://rosettacode.org/wiki/Knuth_shuffle#Haskell
replaceAt :: Int -> a -> [a] -> [a]
replaceAt i c l = let (a,b) = splitAt i l in a++c:(drop 1 b)

swapElems :: (Int, Int) -> [a] -> [a]
swapElems (i,j) xs | i==j = xs
                   | otherwise = replaceAt j (xs!!i) $ replaceAt i (xs!!j) xs

knuthShuffle :: [a] -> IO [a]
knuthShuffle xs =
    liftM (foldr swapElems xs. zip [1..]) (mkRands (length xs))
  where
    mkRands = mapM (randomRIO.(,) 0) . enumFromTo 1 . pred
-- knuthShuffle

allPairs :: [a] -> [b] -> [(a, b)]
allPairs xs ys = pairSearch xs ys
  where
    pairSearch [] _ = []
    pairSearch [_] [] = []
    pairSearch (_:u2:us) [] = pairSearch (u2:us) ys
    pairSearch (u:us) (v:vs) = (u, v) : pairSearch (u:us) vs
-- allPairs

allPairsNonId :: Eq t => [t] -> [t] -> [(t, t)]
allPairsNonId xs ys = pairSearch xs ys
  where
    pairSearch [] _ = []
    pairSearch [_] [] = []
    pairSearch (_:u2:us) [] = pairSearch (u2:us) ys
    pairSearch (u:us) (v:vs) =
        if u == v
        then pairSearch (u:us) vs
        else (u, v) : pairSearch (u:us) vs
-- allPairsNonId

halfOfPairs :: [t] -> [(t, t)]
halfOfPairs xs = pairSearch xs xs
  where
    pairSearch [] _ = []
    pairSearch [_] [] = []
    pairSearch (_:u2:us) [] = pairSearch (u2:us) us
    pairSearch (u:us) (v:vs) = (u, v) : pairSearch (u:us) vs
-- halfOfPairs

halfOfPairsNonId :: Eq t => [t] -> [t] -> [(t, t)]
halfOfPairsNonId xs ys = pairSearch xs ys
  where
    pairSearch [] _ = []
    pairSearch [_] [] = []
    pairSearch (_:u2:us) [] = pairSearch (u2:us) us
    pairSearch (u:us) (v:vs) =
        if u == v
        then pairSearch (u:us) vs
        else (u, v) : pairSearch (u:us) vs
-- halfOfPairsNonId

