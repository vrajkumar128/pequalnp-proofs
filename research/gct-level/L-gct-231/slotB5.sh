cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
while pgrep -f "bash slotB4.sh" >/dev/null; do sleep 10; done
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 4x4_R01_C0 4 4 6 300 701 T
run 4x4_R01_C01 4 4 6 300 702 T
run 4x4_R012_C0 4 4 6 300 703 T
run 4x4_R0_C0_dc 4 4 6 300 704 T
venv/bin/python fast5.py 4 4 6 600 705 > runs4/T_4x4_m6.log 2>&1
venv/bin/python fast5.py 4 5 7 400 706 > runs4/T_4x5_m7.log 2>&1
venv/bin/python fast5.py 4 6 8 200 707 > runs4/T_4x6_m8.log 2>&1
venv/bin/python fast5.py 4 6 8 200 708 r > runs4/T_4x6r_m8.log 2>&1
venv/bin/python fast5.py 4 5 5 3000 709 rc > runs4/T_4x5rc_m5.log 2>&1
