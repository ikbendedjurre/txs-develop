cls
set TXSDIR=C:\Users\WalD1\Documents\_git\txs-develop\
set EXAMPDIR=C:\Users\WalD1\Documents\_git\txs-develop\examps\Adder\
set EXAMPNAME=Adder
set EXPERIMENTDIR=C:\Users\WalD1\Documents\_git\txs-develop\examps\_experiments\

call :CreateTxsInstructions

FOR /L %%x IN (1,1,100) DO (
  call :RunOnce
)

cd %EXAMPSDIR%
exit /B 0

:CreateTxsInstructions
copy /b/v/y %EXAMPDIR%%EXAMPNAME%.txs %EXPERIMENTDIR%
cd %EXPERIMENTDIR%
echo lpe %EXAMPNAME% > _lpeExec.txscmd
echo lpeop step*100-^>info LPE_proxyModel Out >> _lpeExec.txscmd
echo quit >> _lpeExec.txscmd
exit /B 0

:RunOnce
cd %EXPERIMENTDIR%
echo run _lpeExec.txscmd | torxakis %EXAMPNAME%.txs
exit /B 0

