#!/bin/bash
cd "$(dirname "$0")"
K=/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1343/src/kissat/build/kissat
st=$(date +%s.%N)
timeout $2 $K --unsat $1.cnf > $1.kissat_unsat.out 2>&1; rc=$?
en=$(date +%s.%N)
echo "$1 kissat--unsat rc=$rc time=$(echo "$en - $st" | bc)" >> runs.log
