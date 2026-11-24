#!/bin/bash
cd "$(dirname "$0")"
run() { st=$(date +%s.%N); timeout 900 ../src/kissat/build/kissat $1.cnf > $1.out 2>&1; rc=$?; en=$(date +%s.%N); echo "$1 rc=$rc time=$(echo "$en - $st" | bc)" >> sat.log; }
run b22 & run b23; wait
