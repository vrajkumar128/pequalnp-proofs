#!/bin/bash
# NOT-position sweep for one K-local flag case: positions in the given order, cap CAP s each.
# usage: sweep.sh K FLAG CAP pos1 pos2 ...
F=/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/followup-onenot
P=$F/../tool-circuit-synth/venv/bin/python
K=$1; FL=$2; CAP=$3; shift 3
for p in "$@"; do
  L=$F/order3/sweep/${K}_${FL/,/-}_not$p.log
  t0=$(date +%s)
  timeout $CAP $P $F/scripts/kloc5.py $K $FL --notpos $p > $L 2>&1; rc=$?
  t1=$(date +%s)
  [ $rc = 124 ] && echo "no answer within the $CAP s cap (killed by timeout, exit 124)" >> $L
  echo "$(date +%H:%M:%S) $K flag $FL notpos $p: $(grep RESULT $L | cut -c1-120) rc=$rc $((t1-t0))s" >> $F/order3/sweep/sweep.log
done
