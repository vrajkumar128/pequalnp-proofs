#!/usr/bin/env python3
"""Certify UNSAT instances with kissat (text DRAT) + drat-trim; one JSON record per case.
usage: certify.py OUTDIR case.cnf [case2.cnf ...]"""
import hashlib, json, os, subprocess, sys, time
TOOL = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth/third_party/bin'
KISSAT = TOOL + '/kissat'; DRAT = TOOL + '/drat-trim'
KEEP = 100 * 1024 * 1024

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for ch in iter(lambda: f.read(1 << 22), b''):
            h.update(ch)
    return h.hexdigest()

def certify(outdir, cnf):
    name = os.path.basename(cnf)[:-4]
    rec = dict(name=name, cnf=cnf, cnf_sha256=sha(cnf))
    prf = os.path.join(outdir, name + '.drat')
    t0 = time.time()
    r = subprocess.run([KISSAT, '-q', '--no-binary', cnf, prf], capture_output=True, text=True)
    rec['kissat_seconds'] = round(time.time() - t0, 1)
    st = [l for l in r.stdout.splitlines() if l.startswith('s ')]
    rec['kissat_status'] = st[0][2:] if st else 'UNKNOWN'
    if rec['kissat_status'] == 'UNSATISFIABLE':
        rec['proof_bytes'] = os.path.getsize(prf); rec['proof_sha256'] = sha(prf)
        t0 = time.time()
        r = subprocess.run([DRAT, cnf, prf, '-t', '100000'], capture_output=True, text=True)
        rec['drat_seconds'] = round(time.time() - t0, 1)
        rec['drat_trim_tail'] = [l for l in r.stdout.splitlines() if l.startswith('s ') or l.startswith('c ')][-6:]
        rec['drat_trim'] = 's VERIFIED' if any(l.strip() == 's VERIFIED' for l in r.stdout.splitlines()) else 'NOT VERIFIED'
        if rec['proof_bytes'] > KEEP:
            os.remove(prf); rec['proof_stored'] = False
        else:
            subprocess.run(['xz', '-f', '-T1', prf]); rec['proof_stored'] = prf + '.xz'
    json.dump(rec, open(os.path.join(outdir, name + '.json'), 'w'), indent=1)
    print('%s %s kissat %.0fs %s drat %s bytes %s' % (name, rec['kissat_status'], rec['kissat_seconds'],
          rec.get('drat_trim'), rec.get('drat_seconds'), rec.get('proof_bytes')), flush=True)
    return rec

if __name__ == '__main__':
    os.makedirs(sys.argv[1], exist_ok=True)
    for c in sys.argv[2:]:
        certify(sys.argv[1], c)
