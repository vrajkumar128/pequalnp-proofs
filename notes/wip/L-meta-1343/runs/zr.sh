#!/bin/bash
cd "$(dirname "$0")"
run() { st=$(date +%s.%N); timeout 240 ../src/kissat/build/kissat -q $1.cnf > $1.out 2>&1; rc=$?; en=$(date +%s.%N); echo "$1 rc=$rc time=$(echo "$en - $st" | bc)" >> zr.log; }
run zr_c7_9_1 & run zr_c7_9_12; wait
run zr_c7_9_123
