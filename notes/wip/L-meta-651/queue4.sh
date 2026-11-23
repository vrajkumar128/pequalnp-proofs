#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "^./sa_u2 19 1 1901" >/dev/null; do sleep 5; done
./sa_u2_dc 18 1 2818 240 0.6 40000000 1 1000 > u2dc18.log
./sa_u2_dc 17 1 2717 300 0.6 40000000 1 1000 > u2dc17.log
./sa_u2_dc 16 1 2616 400 0.6 40000000 1 1000 > u2dc16.log
./sa_dc 17 1 1717 300 1.0 20000000 1 1000 > dc17.log
