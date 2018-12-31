cls
cd C:\Users\WalD1\Documents\_git\TorXakis\examps

echo lpeop isdet LPE_proxyModel Out > _lpeExec.txscmd
echo exit >> _lpeExec.txscmd

cd Adder
echo run _lpeExec1.txscmd | torxakis Adder.txs
echo run _lpeExec2.txscmd | torxakis MAdder.txs
cd ..

cd Bakery
echo run _lpeExec.txscmd | torxakis bakery.txs
cd ..

cd CustomersOrders
echo run _lpeExec.txscmd | torxakis CustomersOrders.txs
cd ..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro01-processor.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro02-dispatch.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro03-processors.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro04-hide.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro05a-data-nohide.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro05-data.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro06a-datapos-nohide.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro06-datapos.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro07-gcd.txs
cd ../..

cd DispatchProcess\spec
echo run _lpeExec.txscmd | torxakis DisPro08-gcdpurp.txs
cd ../..

cd Echo
echo run _lpeExec.txscmd | torxakis Echo.txs
cd ..

cd Echo
echo run _lpeExec.txscmd | torxakis EchoDelay.txs
cd ..

cd Echo
echo run _lpeExec.txscmd | torxakis LPE.txs
cd ..

cd LuckyPeople/spec
echo run _lpeExec.txscmd | torxakis LuckyPeople.txs
cd ../..

cd MovingArms
echo run _lpeExec.txscmd | torxakis MovingArm.txs
cd ..

cd Point
echo run _lpeExec.txscmd | torxakis Point.txs
cd ..

cd Queue
echo run _lpeExec.txscmd | torxakis Queue.txs
cd ..

cd ReadWriteConflict
echo run _lpeExec.txscmd | torxakis ReadWrite.txs
cd ..

cd StimulusResponse
echo run _lpeExec.txscmd | torxakis StimulusResponse.txs
echo run _lpeExec.txscmd | torxakis StimulusResponseLoop.txs
cd ..






