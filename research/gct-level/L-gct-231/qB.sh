cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
P=$(pgrep -f "fast5.py 4 5 7 300 304"); while [ -n "$P" ] && kill -0 $P 2>/dev/null; do [ $(grep -c normres runs4/T_A_4x5_R01_C01_m7.log) -ge 100 ] && kill $P; sleep 5; done
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 4x5_R012_C0 4 5 7 100 305 T
run 4x5_R0_C012 4 5 7 100 306 T
run 4x5_R0_C0_dc 4 5 7 100 601 T
run 4x5_R01_C0_dc 4 5 7 100 602 T
run 4x5_R012_C01 4 5 7 60 307 T
run 4x6_R01_C0 4 6 7 30 310 C
run 4x6_R01_C0 4 6 8 60 311 T
run 4x6_R0_C01 4 6 8 60 312 T
run 4x6_R01_C01 4 6 8 60 313 T
run 4x6_R012_C0 4 6 8 60 314 T
run 4x6_R0_C012 4 6 8 60 315 T
run 4x6_R0_C0_dc 4 6 8 60 603 T
venv/bin/python fast5.py 4 6 7 30 320 r > runs4/C_4x6r_m7.log 2>&1
run 4x6r_R01_C0 4 6 8 60 321 T
run 4x6r_R0_C01 4 6 8 60 322 T
run 4x6r_R01_C01 4 6 8 60 323 T
run 4x6r_R012_C0 4 6 8 60 324 T
run 4x6r_R0_C012 4 6 8 60 325 T
run 4x6r_R012_C01 4 6 8 60 326 T
run 4x4_R01_C0 4 4 6 100 701 T
run 4x4_R01_C01 4 4 6 100 702 T
run 4x4_R012_C0 4 4 6 100 703 T
run 4x4_R0_C0_dc 4 4 6 100 704 T
venv/bin/python fast5.py 4 5 5 2000 709 rc > runs4/T_4x5rc_m5.log 2>&1
venv/bin/python fast5.py 4 4 6 300 705 > runs4/T_4x4_m6.log 2>&1
venv/bin/python fast5.py 4 5 7 200 706 > runs4/T_4x5_m7.log 2>&1
venv/bin/python fast5.py 4 6 8 100 707 > runs4/T_4x6_m8.log 2>&1
venv/bin/python fast5.py 4 6 8 100 708 r > runs4/T_4x6r_m8.log 2>&1
