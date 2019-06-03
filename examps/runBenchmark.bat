cls
set TXSDIR=C:\Users\WalD1\Documents\_git\txs-develop\

cd /d %TXSDIR%test\sqatt
stack -v --profile bench --ba "--output data20steps.html --csv data20steps.csv"
