#!/bin/bash
cd "$(dirname "$0")"
while pgrep -f "^./sa_sh4 24" >/dev/null; do sleep 5; done
./sa_pool 19 1 999 600 0.5 5000000 1 1 4 pool20_all.txt 20 > pool19.log 2> pool19.err
