#!/usr/bin/env python3
"""drat-trim CNF PROOF; record hashes, time and verdict in cert/NAME.json.
usage: check_proof.py NAME CNF PROOF [keep]"""
import hashlib, json, os, subprocess, sys, time
DRAT = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth/third_party/bin/drat-trim'
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for ch in iter(lambda: f.read(1 << 22), b''):
            h.update(ch)
    return h.hexdigest()
name, cnf, prf = sys.argv[1:4]
rec = dict(name=name, cnf=cnf, cnf_sha256=sha(cnf), proof=prf, proof_bytes=os.path.getsize(prf), proof_sha256=sha(prf))
t0 = time.time()
r = subprocess.run([DRAT, cnf, prf, '-t', '100000'], capture_output=True, text=True)
rec['drat_seconds'] = round(time.time() - t0, 1)
rec['drat_trim_tail'] = [l for l in r.stdout.splitlines() if l.startswith('s ') or l.startswith('c ')][-8:]
rec['verdict'] = 's VERIFIED' if any(l.strip() == 's VERIFIED' for l in r.stdout.splitlines()) else 'NOT VERIFIED'
json.dump(rec, open('cert/%s.json' % name, 'w'), indent=1)
print(name, rec['verdict'], rec['drat_seconds'], 's', rec['proof_bytes'], 'bytes', flush=True)
