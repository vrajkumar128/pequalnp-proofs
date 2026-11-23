#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "^./sa_pool 19" >/dev/null; do sleep 5; done
./sa_dc 19 1 1919 150 1.0 20000000 1 1000 > dc19.log
./sa_dc 18 1 1818 250 1.0 20000000 1 1000 > dc18.log
./sa_dc 17 1 1717 350 1.0 20000000 1 1000 > dc17.log
