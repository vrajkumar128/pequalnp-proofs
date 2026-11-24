#!/bin/bash
cd "$(dirname "$0")"
run() { st=$(date +%s.%N); timeout 240 ../src/kissat/build/kissat -q $1.cnf > $1.out 2>&1; rc=$?; en=$(date +%s.%N); echo "$1 rc=$rc time=$(echo "$en - $st" | bc)" >> cal.log; }
run cal_c7_9_b_inj & run cal_c7_9_b_extra; wait
run cal_c7_9_b_extramono & run cal_c7_9_b_extramonoinj; wait
