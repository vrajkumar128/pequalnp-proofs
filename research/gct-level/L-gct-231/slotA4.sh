cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
while pgrep -f "bash slotA3.sh" >/dev/null; do sleep 10; done
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 5x5_R0_C0_dc 5 5 8 200 501 T
run 5x5_R01_C0_dc 5 5 8 150 502 T
run 5x5_R0_C0_dc 5 5 9 100 503 T
