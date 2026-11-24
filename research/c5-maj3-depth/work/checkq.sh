#!/bin/bash
# drat-trim the given cert names one after another (records cert/NAME.json)
cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1405/work
for n in "$@"; do python3 check_proof.py $n cert/$n.cnf cert/$n.drat; done
