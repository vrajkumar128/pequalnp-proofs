#!/bin/sh
# xz-compress the CNF and DRAT files of the example bundles (recheck reads *.xz directly).
D="$(cd "$(dirname "$0")/.." && pwd)"
find "$D/examples" \( -name '*.cnf' -o -name '*.drat' \) -exec xz -9 -f {} \;
du -sh "$D/examples"
