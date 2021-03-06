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
lpeBenchmarkSet coreName = TxsExampleSet (fromString ("LPE" ++ coreName)) [ example0, example1, example2, example3, example4 ]
  where
    example0 :: TxsExample
    example0 = emptyExample
        { exampleName = coreName ++ " (nothing)"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-original")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-nothing-stepper")) ]
        , expectedResult = Message (Text.pack "")
        }
    
    example1 :: TxsExample
    example1 = emptyExample
        { exampleName = coreName ++ " (stepper on model)"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-original")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper")) ]
        , expectedResult = Pass
        }
    
    example2 :: TxsExample
    example2 = emptyExample
        { exampleName = coreName ++ " (stepper on linear model)"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-original")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper-2")) ]
        , expectedResult = Pass
        }

    example3 :: TxsExample
    example3 = emptyExample
        { exampleName = coreName ++ " (LPEStepper on linear model)"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-lpe-only")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper-3")) ]
        , expectedResult = Pass
        }
    
    example4 :: TxsExample
    example4 = emptyExample
        { exampleName = coreName ++ " (LPEStepper (prep time))"
        , txsModelFiles = [ txsFilePath BenchTest benchDir (Text.pack (coreName ++ "-lpe-only")) ]
        , txsCmdsFiles = [ txsCmdPath BenchTest benchDir (Text.pack (coreName ++ "-original-stepper-4")) ]
        , expectedResult = Pass
        }
-- lpeBenchmarkSet



