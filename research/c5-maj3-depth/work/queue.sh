#!/bin/bash
# run kissat with proof on the given CNFs, one after another; then drat-trim each
K=/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth/third_party/bin/kissat
cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1405/work
for n in "$@"; do
  s=$(date +%s)
  $K -q cert/$n.cnf cert/$n.drat > cert/$n.kissat.out 2>&1
  echo "rc=$? secs=$(( $(date +%s) - s ))" >> cert/$n.kissat.out
  echo "$n $(head -1 cert/$n.kissat.out) $(tail -1 cert/$n.kissat.out)"
done
