#!/bin/sh

./runverit.sh $1
./runverit16.sh $1

vtlog=$(echo $1 | sed "s/.smt2/.vtlog/")
vt16log=$(echo $1 | sed "s/.smt2/.vt16log/")

echo "======================================================="

diff $vtlog $vt16log

echo "======================================================="
