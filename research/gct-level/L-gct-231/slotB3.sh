cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
run() { AMB=ambs/$1.npy venv/bin/python fast5.py $2 $3 $4 $5 $6 > runs4/$7_A_$1_m$4.log 2>&1; }
run 4x5_R01_C0 4 5 6 60 301 C
run 4x5_R01_C0 4 5 7 300 302 T
run 4x5_R0_C01 4 5 7 300 303 T
run 4x5_R01_C01 4 5 7 300 304 T
run 4x5_R012_C0 4 5 7 300 305 T
run 4x5_R0_C012 4 5 7 300 306 T
run 4x5_R012_C01 4 5 7 300 307 T
run 4x6_R01_C0 4 6 8 200 311 T
run 4x6_R0_C01 4 6 8 200 312 T
run 4x6_R01_C01 4 6 8 200 313 T
run 4x6_R012_C0 4 6 8 200 314 T
run 4x6_R0_C012 4 6 8 200 315 T
run 4x6r_R01_C0 4 6 8 200 321 T
run 4x6r_R0_C01 4 6 8 200 322 T
run 4x6r_R01_C01 4 6 8 200 323 T
run 4x6r_R012_C0 4 6 8 200 324 T
run 4x6r_R0_C012 4 6 8 200 325 T
run 4x6r_R012_C01 4 6 8 200 326 T
