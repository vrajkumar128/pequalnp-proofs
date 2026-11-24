cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
P=$(pgrep -f "fast5.py 5 5 8 200 402"); while [ -n "$P" ] && kill -0 $P 2>/dev/null; do [ $(grep -c normres runs4/T_A_5x5_R01_C0_m8.log) -ge 100 ] && kill $P; sleep 5; done
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 5x5_R01_C01 5 5 8 80 403 T
run 5x5_R012_C0 5 5 8 80 404 T
run 5x5_R0_C0_dc 5 5 8 80 501 T
run 5x5_R01_C0_dc 5 5 8 60 502 T
run 5x5_R01_C01 5 5 9 60 405 T
run 5x5_R012_C0 5 5 9 60 406 T
run 5x5_R0_C0_dc 5 5 9 60 503 T
venv/bin/python fast5.py 5 5 8 100 504 > runs4/T_5x5_m8.log 2>&1
venv/bin/python fast5.py 5 5 9 60 505 > runs4/T_5x5_m9.log 2>&1
