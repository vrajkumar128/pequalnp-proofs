#!/bin/sh
# Produce the example certificate bundles and Lean files in examples/ and print timings.
set -e
D="$(cd "$(dirname "$0")/.." && pwd)"
CS="$D/circuit_synth_cli"
E="$D/examples"
mkdir -p "$E"
t() { s=$(date +%s.%N); "$@"; echo "TIME $(echo "$(date +%s.%N) - $s" | bc) :: $*"; }
# certified minimum + Lean file
t "$CS" min --graph 0-1,1-2,2-3 --basis mono --certify --out "$E/P4_mono_min" --lean "$E/P4_mono_min/P4.lean" --name P4
t "$CS" min --n 3 --tt 0xe8 --basis mono --certify --out "$E/maj3_mono_min" --lean "$E/maj3_mono_min/maj3.lean" --name maj3
t "$CS" min --n 2 --tt 0b0110 --basis knot=1 --certify --out "$E/xor2_onenot_min" --lean "$E/xor2_onenot_min/xor2.lean" --name xor2
t "$CS" min --n 3 --tt 0x96 --basis knot=1 --certify --out "$E/xor3_onenot_min" --lean "$E/xor3_onenot_min/xor3.lean" --name xor3_onenot
t "$CS" min --n 3 --tt 0x96 --basis full --certify --out "$E/xor3_full_min" --lean "$E/xor3_full_min/xor3.lean" --name xor3_full
t "$CS" min --sums "0,1,2;1,2,3;0,3" --basis mono --certify --out "$E/sums_min" --lean "$E/sums_min/sums.lean" --name sums
# certified lower bounds
t "$CS" none --graph 0-1,1-2,2-3,3-4,4-0 --basis mono --size 6 --out "$E/C5_mono_none6"
t "$CS" none --graph 0-1,1-2,2-3,3-4,4-0 --basis mono --size 6 --out "$E/C5_mono_none6_raw" --mode raw --rows minterm
t "$CS" none --graph 0-1,1-2,2-3 --basis mono --size 3 --out "$E/P4_mono_none3_raw" --mode raw
t "$CS" min --graph 0-1,1-2,2-3,3-4,4-0 --basis mono --certify --out "$E/C5_mono_min" --lean "$E/C5_mono_min/C5.lean" --name C5
for d in "$E"/*/; do "$CS" recheck "$d" | tail -1; done
