#!/bin/bash
cd "$(dirname "$0")"
for s in 16 17 18 19 20; do
  ../venv/bin/python ../shard_search.py dimacs lad$s.cnf $s --encB --rs=P1,P2,MIS --lcache=lcache_snapshot.json --budget=60 >> ladder.log 2>&1
  st=$(date +%s.%N)
  timeout 480 ../src/kissat/build/kissat -q lad$s.cnf > lad$s.out 2>&1
  rc=$?
  en=$(date +%s.%N)
  echo "s=$s rc=$rc time=$(echo "$en - $st" | bc)" >> ladder.log
  if [ $rc -ne 20 ]; then break; fi
done
