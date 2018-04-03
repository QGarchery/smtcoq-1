#!/bin/sh

./runverit16.sh $1
./runveritdev.sh $1

vt16log=$(echo $1 | sed "s/.smt2/.vt16log/")
vtdevlog=$(echo $1 | sed "s/.smt2/.vtdevlog/")

echo "======================================================="

diff $vt16log $vtdevlog

echo "======================================================="
