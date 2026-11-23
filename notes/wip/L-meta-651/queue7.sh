#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "^./sa_dc 19" >/dev/null; do sleep 5; done
./sa_dc 20 1 2020 150 1.0 20000000 1 1000 > dc20.log
./sa_dc 17 1 1717 300 1.0 20000000 1 1000 > dc17.log
