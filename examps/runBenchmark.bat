cls
set TXSDIR=C:\Users\WalD1\Documents\_git\txs-develop\

cd /d %TXSDIR%test\sqatt
stack -v --profile bench --ba "--output data100loggedsteps.html --csv data100loggedsteps.csv"
