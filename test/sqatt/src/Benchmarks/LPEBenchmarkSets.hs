{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}
{-# LANGUAGE OverloadedStrings #-}
module Benchmarks.LPEBenchmarkSets (lpeBenchmarkSet) where

--import           Benchmarks.Common
import           Paths
import           Prelude           hiding (FilePath)
import           Sqatt
import qualified Data.Text as Text

benchDir :: FilePath
benchDir = "LPE"

-- lpeBenchmarkSet :: String -> TxsExampleSet
-- lpeBenchmarkSet coreName = TxsExampleSet (fromString ("LPE" ++ coreName)) [ example1, example2, example3 ]
  -- where
    -- example1 :: TxsExample
    -- example1 = emptyExample
        -- { exampleName = coreName ++ "-original"
        -- , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-original")) ]
        -- , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper")) ]
        -- , expectedResult = Pass
        -- }
    
    -- example2 :: TxsExample
    -- example2 = emptyExample
        -- { exampleName = coreName ++ "-lpe-only"
        -- , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-lpe-only")) ]
        -- , txsCmdsFiles = [ txsCmdPath BenchTest benchDir "Test" ]
        -- , expectedResult = Pass
        -- }

    -- example3 :: TxsExample
    -- example3 = emptyExample
        -- { exampleName = coreName ++ "-lpe-reduced"
        -- , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-lpe-reduced")) ]
        -- , txsCmdsFiles = [ txsCmdPath BenchTest benchDir "Test" ]
        -- , expectedResult = Pass
        -- }
-- -- lpeBenchmarkSet

lpeBenchmarkSet :: String -> TxsExampleSet
lpeBenchmarkSet coreName = TxsExampleSet (fromString ("LPE" ++ coreName)) [ example1, example2, example3 ]
  where
    example1 :: TxsExample
    example1 = emptyExample
        { exampleName = coreName ++ " (stepper)"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-original")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper")) ]
        , expectedResult = Pass
        }

    example2 :: TxsExample
    example2 = emptyExample
        { exampleName = coreName ++ " (LPEStepper)"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-lpe-only")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper-2")) ]
        , expectedResult = Pass
        }
    
    example3 :: TxsExample
    example3 = emptyExample
        { exampleName = coreName ++ " (ReducedLPEStepper)"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-lpe-reduced")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper-3")) ]
        , expectedResult = Pass
        }
-- lpeBenchmarkSet



