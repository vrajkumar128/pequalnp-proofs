#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "^./sa_u2 19 1 1901" >/dev/null; do sleep 5; done
./sa4 19 1 505 600 1.0 20000000 1 2 4 > sa19_not2.log
./sa_u2 19 1 1902 600 0.6 40000000 1 1000 4 > u2_19b.log
