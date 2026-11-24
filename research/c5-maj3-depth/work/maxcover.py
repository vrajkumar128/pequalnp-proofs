#!/usr/bin/env python3
"""Is there a depth-D formula that rejects every Bob row and accepts >= k minterms (side a),
or accepts every minterm and rejects >= k Bob rows (side b)?"""
import sys, os, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen, run
ap = argparse.ArgumentParser()
ap.add_argument('--fn', default='c5'); ap.add_argument('--D', type=int, default=5)
ap.add_argument('--side', default='a'); ap.add_argument('--k', type=int, required=True); ap.add_argument('--k2', type=int, default=0)
ap.add_argument('--sbvar', type=int, default=4); ap.add_argument('--prec', type=int, default=1); ap.add_argument('--refl', type=int, default=1)
ap.add_argument('--out', required=True); ap.add_argument('--timeout', type=float, default=None)
ap.add_argument('--nosolve', type=int, default=0); ap.add_argument('--cube', default='')
a = ap.parse_args()
sp = gen.spec(a.fn)
ar = list(range(len(sp['A']))); br = list(range(len(sp['B'])))
c, info = gen.build(sp, a.D, ar, br, sb_swap='ts', sb_var=a.sbvar, sb_prec=bool(a.prec), sb_refl=bool(a.refl), free_side=a.side, atleast_k=(a.k, a.k2) if a.side == 'ab' else a.k, cube={i + 1: int(ch) for i, ch in enumerate(a.cube) if ch in '01'})
gen.write(c, a.out, comments=['depth %d side %s at least %d' % (a.D, a.side, a.k)])
print('vars', c.nv, 'clauses', len(c.cls), flush=True)
if a.nosolve: sys.exit(0)
st, model, dt = run.solve(a.out, a.timeout)
print(st, '%.1fs' % dt, flush=True)
if st == 'SATISFIABLE':
    fm = gen.decode(model, info, sp['n'])
    acc = sum(gen.ev(fm, t) for t in sp['A']); rej = sum(1 - gen.ev(fm, t) for t in sp['B'])
    print('depth', gen.depth(fm), 'accepted minterms', acc, 'rejected bob rows', rej)
    print(gen.show(fm))
