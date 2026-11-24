#!/bin/bash
cd "$(dirname "$0")"
for f in cyc7_a_9 cyc7_b_9 cyc8_a_10 cyc8_b_10 cyc9_a_12 cyc9_b_12; do
  st=$(date +%s.%N)
  timeout 300 ../src/kissat/build/kissat -q $f.cnf > $f.out 2>&1
  rc=$?
  en=$(date +%s.%N)
  echo "$f rc=$rc time=$(echo "$en - $st" | bc)" >> cyc.log
done
