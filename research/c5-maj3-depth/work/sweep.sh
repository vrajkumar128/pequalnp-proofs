#!/bin/bash
# usage: sweep.sh TLIMIT cube...   (runs 2 at a time)
S=/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad
W=$S/L-meta-1405/work
TL=$1; shift
for c in "$@"; do
  while [ $(pgrep -f "^/.*venv519/bin/python .*cegar.py --D 6 --cube" | wc -l) -ge 2 ]; do sleep 2; done
  ( timeout $TL $S/venv519/bin/python $W/cegar.py --D 6 --cube $c --seed 7 --save $W/sweep/$c.json > $W/sweep/$c.log 2>&1; echo "$c rc=$? $(tail -n 2 $W/sweep/$c.log | tr '\n' ' ')" >> $W/sweep/summary.txt ) &
  sleep 1
done
wait
