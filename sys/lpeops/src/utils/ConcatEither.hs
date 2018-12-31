{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and University of Twente
See LICENSE at root directory of this repository.
-}

-----------------------------------------------------------------------------
-- |
-- Module      :  ConcatEither
-- Copyright   :  TNO and University of Twente
-- License     :  BSD3
-- Maintainer  :  djurrevanderwal@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------

module ConcatEither (
concatEither
) where

concatEither :: [Either [a] [b]] -> Either [a] [b]
concatEither [] = Right []
concatEither (Left xs:ys) =
    case concatEither ys of
      Left zs -> Left (xs ++ zs)
      Right _ -> Left xs
concatEither (Right xs:ys) =
    case concatEither ys of
      Left zs -> Left zs
      Right zs -> Right (xs ++ zs)
-- concatEither

