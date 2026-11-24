#!/bin/bash
cd "$(dirname "$0")"
for s in 12 13 14; do for e in a b i bi; do
  st=$(date +%s.%N)
  timeout 600 ../src/kissat/build/kissat -q $e$s.cnf > $e$s.out 2>&1
  rc=$?
  en=$(date +%s.%N)
  echo "$e s=$s rc=$rc time=$(echo "$en - $st" | bc)" >> cmp.log
done; done
