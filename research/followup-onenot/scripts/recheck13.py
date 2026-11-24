"""Recheck the size-13 case bundle: regenerate base and case CNFs with the circuit_synth encoder
(via fano13_cases.py into a temporary directory), compare SHA-256 with cases.json and with the
per-case results, and re-run drat-trim on every stored proof (plain or .xz).

usage: recheck13.py BUNDLE_DIR [--no-drat]
"""
import json
import lzma
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fano13_cases  # noqa: E402
from run_cases import sha, DRAT  # noqa: E402


def main(d, drat=True):
    info = json.load(open(os.path.join(d, 'cases.json')))
    tmp = tempfile.mkdtemp(prefix='recheck13_', dir=d)
    ok = True
    try:
        fano13_cases.main(tmp)
        new = json.load(open(os.path.join(tmp, 'cases.json')))
        same = new['base_cnf_sha256'] == info['base_cnf_sha256']
        print('base CNF regenerated: sha256 %s' % ('matches' if same else 'DIFFERS'))
        ok &= same
        for c_old, c_new in zip(info['cases'], new['cases']):
            r = json.load(open(os.path.join(d, 'results', c_old['name'] + '.json')))
            same = c_old['cnf_sha256'] == c_new['cnf_sha256'] == r['cnf_sha256'] == \
                sha(os.path.join(tmp, c_new['cnf']))
            line = '%-22s CNF %s, kissat %s' % (c_old['name'], 'matches' if same else 'DIFFERS',
                                               r['kissat_status'])
            ok &= same and r['kissat_status'] == 'UNSATISFIABLE' and r['drat_trim'] == 's VERIFIED'
            prf = os.path.join(d, 'case_%s.drat' % c_old['name'])
            if drat and (os.path.exists(prf) or os.path.exists(prf + '.xz')):
                if not os.path.exists(prf):
                    p2 = os.path.join(tmp, os.path.basename(prf))
                    with lzma.open(prf + '.xz') as fi, open(p2, 'wb') as fo:
                        shutil.copyfileobj(fi, fo)
                    prf = p2
                sp = sha(prf) == r['proof_sha256']
                out = subprocess.run([DRAT, os.path.join(tmp, c_new['cnf']), prf, '-t', '100000'],
                                     capture_output=True, text=True).stdout
                v = any(l.strip() == 's VERIFIED' for l in out.splitlines())
                line += ', proof sha256 %s, drat-trim: %s' % ('matches' if sp else 'DIFFERS',
                                                              's VERIFIED' if v else 'NOT VERIFIED')
                ok &= sp and v
            elif os.path.exists(prf) or os.path.exists(prf + '.xz'):
                line += ', proof stored, drat-trim not re-run (--no-drat; recorded: %s)' % r['drat_trim']
            else:
                line += ', proof not stored (sha256 %s..., recorded drat-trim: %s)' % (
                    r['proof_sha256'][:16], r['drat_trim'])
            print(line, flush=True)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print('recheck size-13 bundle: %s' % ('OK' if ok else 'FAILED'))
    return ok


if __name__ == '__main__':
    main(sys.argv[1], '--no-drat' not in sys.argv)
