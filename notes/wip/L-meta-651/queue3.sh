#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "^./sa_u2 19 1 1901" >/dev/null; do sleep 5; done
./sa_dc 18 1 1818 300 1.0 20000000 1 1000 > dc18.log
./sa_dc 17 1 1717 600 1.0 20000000 1 1000 > dc17.log
./sa4 19 1 505 400 1.0 20000000 1 2 4 > sa19_not2.log
