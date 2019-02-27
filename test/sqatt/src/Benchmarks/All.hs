{-
TorXakis - Model Based Testing
Copyright (c) 2015-2017 TNO and Radboud University
See LICENSE at root directory of this repository.
-}

module Benchmarks.All (allExamples, allBenchmarks) where

--import qualified Benchmarks.Choice          as Choice
--import qualified Benchmarks.Dynamic         as Dynamic
--import qualified Benchmarks.Enable          as Enable
--import qualified Benchmarks.Hiding          as Hiding
--import qualified Benchmarks.Parallel        as Parallel
import qualified Benchmarks.LPEBenchmarkSets      as LPEBenchmarkSets
--import qualified Benchmarks.Queue           as Queue
--import qualified Benchmarks.RealWorld       as RealWorld
--import qualified Benchmarks.Sequence        as Sequence
--import qualified Benchmarks.Synchronization as Synchronization
import           Criterion.Main
import           Sqatt

allExamples :: [TxsExampleSet]
allExamples = [ --Choice.benchmarksSet
              --, Dynamic.benchmarksSet
              --, Enable.benchmarksSet
              --, Hiding.benchmarksSet
              --, RealWorld.benchmarksSet
              --, Sequence.benchmarksSet
              --, Synchronization.benchmarksSet
              --, Queue.benchmarksSet
                LPEBenchmarkSets.lpeBenchmarkSet "Adder" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "Adder3" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "Bakery" -- Works
              --  LPEBenchmarkSets.lpeBenchmarkSet "SpeedTest" -- 
              , LPEBenchmarkSets.lpeBenchmarkSet "ControlLoop" -- Fails because of hidden variables?
              --, LPEBenchmarkSets.lpeBenchmarkSet "CustomersOrders" -- Takes too long!
              , LPEBenchmarkSets.lpeBenchmarkSet "DisPro01" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "DisPro02" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "DisPro03" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "DisPro04" -- Works
              --, LPEBenchmarkSets.lpeBenchmarkSet "DisPro05a" -- Takes too long!
              --, LPEBenchmarkSets.lpeBenchmarkSet "DisPro05" -- Fails because of hidden variables?
              --, LPEBenchmarkSets.lpeBenchmarkSet "DisPro06a" -- Takes too long!
              --, LPEBenchmarkSets.lpeBenchmarkSet "DisPro06" -- Fails because of hidden variables?
              --, LPEBenchmarkSets.lpeBenchmarkSet "DisPro07" -- Fails because of hidden variables?
              --, LPEBenchmarkSets.lpeBenchmarkSet "DisPro08" -- Fails because of hidden variables?
              , LPEBenchmarkSets.lpeBenchmarkSet "Echo" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "EchoDelay" -- Works (sometimes fails?!)
              , LPEBenchmarkSets.lpeBenchmarkSet "Lossy" -- Works (sometimes fails?!)
              --, LPEBenchmarkSets.lpeBenchmarkSet "LuckyPeople" -- Takes too long!
              , LPEBenchmarkSets.lpeBenchmarkSet "MAdder" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "MovingArm" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "Queue" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "ReadWrite" -- Works
              , LPEBenchmarkSets.lpeBenchmarkSet "StimulusResponseLoop" -- Works
              --, LPEBenchmarkSets.lpeBenchmarkSet "StimulusResponse" -- Too short, quiescence!
              ]

allBenchmarks :: [Benchmark]
allBenchmarks = benchmarkExampleSet <$> allExamples
