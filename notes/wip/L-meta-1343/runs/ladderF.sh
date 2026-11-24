#!/bin/bash
cd "$(dirname "$0")"
for s in 16 17 18; do
  ../venv/bin/python ../shard_search.py dimacs ladF$s.cnf $s --encB --rs=P1,P2,P1Q1,MIS --lcache=lcache_full_snapshot.json --budget=60 >> ladderF.log 2>&1
  st=$(date +%s.%N)
  timeout 480 ../src/kissat/build/kissat -q ladF$s.cnf > ladF$s.out 2>&1
  rc=$?
  en=$(date +%s.%N)
  echo "s=$s rc=$rc time=$(echo "$en - $st" | bc)" >> ladderF.log
  if [ $rc -ne 20 ]; then break; fi
done
