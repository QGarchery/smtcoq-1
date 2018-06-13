#!/bin/sh

./runverit.sh $1
./runveritdev.sh $1

vtlog=$(echo $1 | sed "s/.smt2/.vtlog/")
vtdevlog=$(echo $1 | sed "s/.smt2/.vtdevlog/")

echo "======================================================="

diff $vtlog $vtdevlog

echo "======================================================="
