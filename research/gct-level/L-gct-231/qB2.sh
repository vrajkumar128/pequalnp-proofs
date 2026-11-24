cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
while pgrep -f "fast5.py 4 6 8 60 311" >/dev/null; do sleep 5; done
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 4x4_R01_C0 4 4 6 100 701 T
run 4x4_R01_C01 4 4 6 100 702 T
run 4x4_R012_C0 4 4 6 100 703 T
run 4x4_R0_C0_dc 4 4 6 100 704 T
venv/bin/python fast5.py 4 6 7 30 320 r > runs4/C_4x6r_m7.log 2>&1
run 4x6r_R01_C0 4 6 8 40 321 T
run 4x6r_R0_C01 4 6 8 40 322 T
run 4x6r_R012_C0 4 6 8 40 324 T
run 4x6r_R01_C01 4 6 8 40 323 T
run 4x6_R0_C01 4 6 8 40 312 T
run 4x6_R01_C01 4 6 8 40 313 T
run 4x6_R0_C0_dc 4 6 8 40 603 T
run 4x6_R012_C0 4 6 8 40 314 T
venv/bin/python fast5.py 4 4 6 300 705 > runs4/T_4x4_m6.log 2>&1
venv/bin/python fast5.py 4 5 5 2000 709 rc > runs4/T_4x5rc_m5_b.log 2>&1
