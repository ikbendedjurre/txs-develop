{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
import           Benchmarks.All
import           Criterion.Main
import           Criterion.Types

main :: IO ()
main = defaultMainWith cfg allBenchmarks
  where
    cfg = defaultConfig { rawDataFile = Just "please-be-there.raw"
                        , reportFile = Just "please-be-there.report"
                        }
-- main

