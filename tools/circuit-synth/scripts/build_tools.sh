#!/bin/sh
# Build the external tools into third_party/bin: kissat, CaDiCaL (solvers with DRAT proof
# output) and drat-trim (proof checker). python-sat (pip) is optional and only speeds up
# uncertified runs and the validation suite.
#   scripts/build_tools.sh            # all three
# Versions used for the recorded results: kissat 4.0.4, CaDiCaL 2.1.3,
# drat-trim commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985.
set -e
D="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$D/third_party/bin"
cd "$D/third_party"
[ -d drat-trim ] || git clone --depth 1 https://github.com/marijnheule/drat-trim
(cd drat-trim && make drat-trim && cp drat-trim ../bin/)
[ -d kissat ] || git clone --depth 1 --branch rel-4.0.4 https://github.com/arminbiere/kissat
(cd kissat && ./configure && make -j2 && cp build/kissat ../bin/)
[ -d cadical ] || git clone --depth 1 --branch rel-2.1.3 https://github.com/arminbiere/cadical
(cd cadical && ./configure && make -j2 && cp build/cadical ../bin/)
"$D/third_party/bin/kissat" --version
"$D/third_party/bin/cadical" --version
echo "tools in $D/third_party/bin"
