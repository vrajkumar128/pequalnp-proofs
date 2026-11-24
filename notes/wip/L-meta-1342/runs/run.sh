#!/bin/bash
# run.sh NAME SOLVER TIMEOUT
cd "$(dirname "$0")"
K=/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1343/src/kissat/build/kissat
C=/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1343/src/cadical/build/cadical
st=$(date +%s.%N)
if [ "$2" = kissat ]; then timeout $3 $K $1.cnf > $1.$2.out 2>&1; rc=$?; else timeout $3 $C $1.cnf > $1.$2.out 2>&1; rc=$?; fi
en=$(date +%s.%N)
echo "$1 $2 rc=$rc time=$(echo "$en - $st" | bc)" >> runs.log
