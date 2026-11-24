cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
while pgrep -f "bash slotB3.sh" >/dev/null; do sleep 10; done
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 4x5_R0_C0_dc 4 5 7 300 601 T
run 4x5_R01_C0_dc 4 5 7 300 602 T
run 4x6_R0_C0_dc 4 6 8 200 603 T
