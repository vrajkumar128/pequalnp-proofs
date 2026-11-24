#!/bin/bash
cd "$(dirname "$0")"
for s in 16 17 18 19 20; do
  st=$(date +%s.%N)
  timeout 3000 ../src/kissat/build/kissat -q a$s.cnf > a$s.out 2>&1
  rc=$?
  en=$(date +%s.%N)
  echo "s=$s rc=$rc time=$(echo "$en - $st" | bc)" >> scale.log
done
