set TXSDIR=C:\Users\WalD1\Documents\_git\txs-develop\
set BENCHDIR=%TXSDIR%\test\sqatt\data\bench\LPE\

cls
cd %TXSDIR%\examps

cd Adder
call :WriteAndExec Adder Adder Adder
call :WriteAndExec Adder Adder3 Adder3
call :WriteAndExec MAdder Adder MAdder
cd ..

cd Bakery
call :WriteAndExec bakery Model Bakery
cd ..

cd ControlLoop
call :WriteAndExec ControlLoopModel Model ControlLoop
cd ..

cd CustomersOrders
call :WriteAndExec CustomersOrders Model CustomersOrders
cd ..

cd DispatchProcess\spec
call :WriteAndExec DisPro01-processor Model DisPro01
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro02-dispatch Model DisPro02
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro03-processors Model DisPro03
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro04-hide Model DisPro04
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro05a-data-nohide Model DisPro05a
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro05-data Model DisPro05
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro06a-datapos-nohide Model DisPro06a
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro06-datapos Model DisPro06
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro07-gcd Model DisPro07
cd ../..

cd DispatchProcess\spec
call :WriteAndExec DisPro08-gcdpurp Model DisPro08
cd ../..

cd Echo
call :WriteAndExec Echo Model Echo
cd ..

cd Echo
call :WriteAndExec EchoDelay Model EchoDelay
cd ..

cd LuckyPeople/spec
call :WriteAndExec LuckyPeople Model LuckyPeople
cd ../..

cd MovingArms
call :WriteAndExec MovingArm Model MovingArm
cd ..

cd Point
call :WriteAndExec Point Model Point
cd ..

cd Queue
call :WriteAndExec Queue Queue Queue
call :WriteAndExec Queue Lossy Lossy
cd ..

cd ReadWriteConflict
call :WriteAndExec ReadWrite Model ReadWrite
cd ..

cd StimulusResponse
call :WriteAndExec StimulusResponse Model StimulusResponse
call :WriteAndExec StimulusResponseLoop Model StimulusResponseLoop
cd ..

exit /B 0

:WriteCommands
echo lpe %~1 > _lpeExec.txscmd
echo lpeop export* LPE_proxyModel %~2-lpe-only >> _lpeExec.txscmd
::echo lpeop confelm-^>export* LPE_proxyModel %~2-lpe-reduced >> _lpeExec.txscmd
::echo lpeop clean-^>cstelm-^>parelm-^>parreset-^>datareset-^>loop-^>export* LPE_proxyModel %~2-lpe-reduced >> _lpeExec.txscmd
echo quit >> _lpeExec.txscmd
exit /B 0

:DeleteCommands
del /q _lpeExec.txscmd
exit /B 0

:WriteAndExec
:: Copy the original model to the benchmark directory
copy /b/v/y %~1.txs %BENCHDIR%
del /q %BENCHDIR%%~3-original.txs
ren %BENCHDIR%%~1.txs %~3-original.txs
:: Generate new models from the original model and copy them to the benchmark directory
:: call :WriteCommands "%~2" "%~3"
:: echo run _lpeExec.txscmd | torxakis %~1.txs
:: move /y %~3-lpe-only.txs %BENCHDIR%
:: move /y %~3-lpe-reduced.txs %BENCHDIR%
:: call :DeleteCommands
:: Create a file that instructs the benchmark on how to test the ORIGINAL model (because its model name may be different for each file)
echo stepper %~2 > %BENCHDIR%%~3-original-stepper.txscmd
echo step 20 >> %BENCHDIR%%~3-original-stepper.txscmd
echo exit >> %BENCHDIR%%~3-original-stepper.txscmd
echo lpe %~2 > %BENCHDIR%%~3-original-stepper-2.txscmd
echo stepper LPE_proxyModel >> %BENCHDIR%%~3-original-stepper-2.txscmd
echo step 20 >> %BENCHDIR%%~3-original-stepper-2.txscmd
echo exit >> %BENCHDIR%%~3-original-stepper-2.txscmd
echo lpe Model > %BENCHDIR%%~3-original-stepper-3.txscmd
echo lpeop step*20 LPE_proxyModel Dummy >> %BENCHDIR%%~3-original-stepper-3.txscmd
echo exit >> %BENCHDIR%%~3-original-stepper-3.txscmd
echo lpe Model > %BENCHDIR%%~3-original-stepper-4.txscmd
echo lpeop step*0 LPE_proxyModel Dummy >> %BENCHDIR%%~3-original-stepper-4.txscmd
echo exit >> %BENCHDIR%%~3-original-stepper-4.txscmd
exit /B 0

