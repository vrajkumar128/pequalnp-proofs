#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "^./sa_u2_dc 18" >/dev/null; do sleep 5; done
./sa_u2_dc 20 1 2020 200 0.6 40000000 1 1000 > u2dc20.log
./sa_u2_dc 17 1 2717 300 0.6 40000000 1 1000 > u2dc17.log
./sa_u2_dc 16 1 2616 300 0.6 40000000 1 1000 > u2dc16.log
