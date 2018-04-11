#!/bin/sh

./runverit16.sh $1
./runveritlast.sh $1

vt16log=$(echo $1 | sed "s/.smt2/.vt16log/")
vtlastlog=$(echo $1 | sed "s/.smt2/.vtlastlog/")

echo "======================================================="

diff $vt16log $vtlastlog

echo "======================================================="
