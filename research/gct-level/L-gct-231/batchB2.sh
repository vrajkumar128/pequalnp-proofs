cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231
while kill -0 24011 2>/dev/null; do sleep 5; done
venv/bin/python search3.py 4 4 4 40 32 rc > runs3/4x4rc_m4.log 2>&1
venv/bin/python search3.py 4 4 3 10 31 rc > runs3/4x4rc_m3.log 2>&1
venv/bin/python search3.py 4 5 5 40 30 rc > runs3/4x5rc_m5.log 2>&1
venv/bin/python search3.py 4 5 4 10 29 rc > runs3/4x5rc_m4.log 2>&1
venv/bin/python search3.py 4 6 8 25 28 r > runs3/4x6r_m8.log 2>&1
venv/bin/python search3.py 4 6 7 10 27 r > runs3/4x6r_m7.log 2>&1
venv/bin/python search3.py 4 6 8 25 26 > runs3/4x6_m8.log 2>&1
venv/bin/python search3.py 4 6 7 10 25 > runs3/4x6_m7.log 2>&1
venv/bin/python search3.py 4 5 8 15 23 > runs3/4x5_m8.log 2>&1
venv/bin/python search3.py 4 4 6 30 24 > runs3/4x4_m6.log 2>&1
