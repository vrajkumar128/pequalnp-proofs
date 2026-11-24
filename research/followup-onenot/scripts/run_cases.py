"""Run the case CNFs of cases.json: kissat 4.0.4 (-q --no-binary, text DRAT proof), then
drat-trim CNF PROOF -t 100000. One JSON record per case in DIR/results/. The number of
parallel workers is read from DIR/NWORK before each dispatch (so it can be raised later).
Proofs larger than KEEP_BYTES are deleted after their SHA-256 is recorded (kissat is
single-threaded and deterministic: the same binary on the same CNF regenerates them).

usage: run_cases.py DIR [case-name ...]   (default: all cases not yet done, in cases.json order)
"""
import hashlib
import json
import os
import subprocess
import sys
import threading
import time

TOOL = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth'
KISSAT = TOOL + '/third_party/bin/kissat'
DRAT = TOOL + '/third_party/bin/drat-trim'
KEEP_BYTES = 150 * 1024 * 1024


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 22), b''):
            h.update(chunk)
    return h.hexdigest()


def run_case(d, c):
    cnf = os.path.join(d, c['cnf'])
    prf = os.path.join(d, 'case_%s.drat' % c['name'])
    rec = {'name': c['name'], 'cnf': c['cnf'], 'cube': c['cube'], 'desc': c['desc']}
    rec['cnf_sha256'] = sha(cnf)
    assert rec['cnf_sha256'] == c['cnf_sha256']
    t0 = time.time()
    r = subprocess.run([KISSAT, '-q', '--no-binary', cnf, prf], capture_output=True, text=True)
    rec['kissat_seconds'] = round(time.time() - t0, 1)
    st = [l for l in r.stdout.splitlines() if l.startswith('s ')]
    rec['kissat_status'] = st[0][2:] if st else 'UNKNOWN (rc %d)' % r.returncode
    rec['kissat_cmd'] = 'kissat -q --no-binary %s %s' % (c['cnf'], os.path.basename(prf))
    if rec['kissat_status'] == 'UNSATISFIABLE':
        rec['proof_bytes'] = os.path.getsize(prf)
        rec['proof_sha256'] = sha(prf)
        t0 = time.time()
        r = subprocess.run([DRAT, cnf, prf, '-t', '100000'], capture_output=True, text=True)
        rec['drat_seconds'] = round(time.time() - t0, 1)
        rec['drat_trim_cmd'] = 'drat-trim %s %s -t 100000' % (c['cnf'], os.path.basename(prf))
        rec['drat_trim_output'] = [l for l in r.stdout.splitlines()
                                   if l.startswith('s ') or l.startswith('c ')][-12:]
        rec['drat_trim'] = 's VERIFIED' if any(l.strip() == 's VERIFIED'
                                               for l in r.stdout.splitlines()) else 'NOT VERIFIED'
        if rec['proof_bytes'] > KEEP_BYTES:
            os.remove(prf)
            rec['proof_stored'] = False
        else:
            rec['proof_stored'] = True
    else:
        rec['kissat_stdout'] = r.stdout[-2000:]
    with open(os.path.join(d, 'results', c['name'] + '.json'), 'w') as f:
        json.dump(rec, f, indent=1)
    print('%s %s: %s kissat %.0fs drat %s %ss proof %s bytes' % (
        time.strftime('%H:%M:%S'), c['name'], rec['kissat_status'], rec['kissat_seconds'],
        rec.get('drat_trim'), rec.get('drat_seconds'), rec.get('proof_bytes')), flush=True)


def main():
    d = sys.argv[1]
    with open(os.path.join(d, 'cases.json')) as f:
        info = json.load(f)
    os.makedirs(os.path.join(d, 'results'), exist_ok=True)
    want = sys.argv[2:]
    todo = [c for c in info['cases'] if (not want or c['name'] in want)
            and not os.path.exists(os.path.join(d, 'results', c['name'] + '.json'))]
    if want:
        todo.sort(key=lambda c: want.index(c['name']))
    running = []
    while todo or running:
        running = [t for t in running if t.is_alive()]
        try:
            nw = int(open(os.path.join(d, 'NWORK')).read().strip())
        except Exception:
            nw = 1
        if todo and len(running) < nw:
            c = todo.pop(0)
            print('%s start %s' % (time.strftime('%H:%M:%S'), c['name']), flush=True)
            t = threading.Thread(target=run_case, args=(d, c))
            t.start()
            running.append(t)
            continue
        time.sleep(2)


if __name__ == '__main__':
    main()
