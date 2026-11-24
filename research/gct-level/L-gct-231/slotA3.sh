cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
while pgrep -f "L_gct_181.lean" >/dev/null; do sleep 5; done
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 5x5_R01_C0 5 5 7 40 401 C
run 5x5_R01_C0 5 5 8 200 402 T
run 5x5_R01_C01 5 5 8 200 403 T
run 5x5_R012_C0 5 5 8 200 404 T
run 5x5_R01_C01 5 5 9 150 405 T
run 5x5_R012_C0 5 5 9 150 406 T
