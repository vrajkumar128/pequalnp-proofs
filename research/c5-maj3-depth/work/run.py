#!/usr/bin/env python3
import sys, subprocess, time, argparse, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen

KISSAT = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/tool-circuit-synth/third_party/bin/kissat'

def solve(path, timeout=None, extra=()):
    t0 = time.time()
    try:
        p = subprocess.run([KISSAT, '-q'] + list(extra) + [path], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', None, time.time() - t0
    st = None; model = []
    for line in p.stdout.splitlines():
        if line.startswith('s '):
            st = line[2:].strip()
        elif line.startswith('v '):
            model += [int(x) for x in line[2:].split() if x != '0']
    return st, model, time.time() - t0

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--fn', default='c5'); ap.add_argument('--D', type=int, default=6)
    ap.add_argument('--na', type=int, default=-1); ap.add_argument('--nbr', type=int, default=-1)
    ap.add_argument('--sb', default='ts'); ap.add_argument('--sbrows', type=int, default=0)
    ap.add_argument('--sbvar', type=int, default=4); ap.add_argument('--cube', default='')
    ap.add_argument('--enc', default='kw'); ap.add_argument('--prec', type=int, default=0); ap.add_argument('--refl', type=int, default=0); ap.add_argument('--timeout', type=float, default=None); ap.add_argument('--out', default='/tmp/x.cnf')
    a = ap.parse_args()
    sp = gen.spec(a.fn)
    ar = list(range(len(sp['A']))) if a.na < 0 else list(range(a.na))
    br = list(range(len(sp['B']))) if a.nbr < 0 else list(range(a.nbr))
    cube = {}
    if a.cube:
        for i, ch in enumerate(a.cube):
            if ch in '01':
                cube[i + 1] = int(ch)
    c, info = gen.build(sp, a.D, ar, br, sb_swap=a.sb, sb_rows=a.sbrows, sb_var=a.sbvar, cube=cube, enc=a.enc, sb_prec=bool(a.prec), sb_refl=bool(a.refl))
    gen.write(c, a.out)
    print('vars', c.nv, 'clauses', len(c.cls), 'base', info['nbase'], 'varSB', info['nvarcl'], flush=True)
    st, model, dt = solve(a.out, a.timeout)
    print(st, '%.1fs' % dt, flush=True)
    if st == 'SATISFIABLE':
        fm = gen.decode(model, info, sp['n'])
        ok = all(gen.ev(fm, x) == sp['tt'][x] for x in range(1 << sp['n']))
        print('depth', gen.depth(fm), 'correct on all inputs:', ok)
        print(gen.show(fm))
