#!/usr/bin/env python3
"""Given a set S of minterm indices (or Bob row indices), test whether the complement is
depth-D separable against all rows of the other side (kissat, swap SB only)."""
import sys, os, json, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen, run
ap = argparse.ArgumentParser(); ap.add_argument('--D', type=int, default=5); ap.add_argument('--side', default='a')
ap.add_argument('--set', required=True); ap.add_argument('--out', required=True); ap.add_argument('--timeout', type=float, default=None)
a = ap.parse_args()
sp = gen.spec('c5')
S = set(json.loads(a.set))
if a.side == 'a':
    ar = [r for r in range(45) if r not in S]; br = list(range(135))
else:
    ar = list(range(45)); br = [r for r in range(135) if r not in S]
from rootsplit import group_perms, apply_mask
G = group_perms(sp)
rows = sp['A'] if a.side == 'a' else sp['B']
idx = {t: r for r, t in enumerate(rows)}
Sf = frozenset(S)
H = [p for p in G if frozenset(idx[apply_mask(p, rows[r])] for r in S) == Sf]
print('stabilizer order', len(H), flush=True)
c, info = gen.build(sp, a.D, ar, br, sb_swap='ts', sb_var=0, subgroup=H)
gen.write(c, a.out)
print('rows', len(ar), len(br), 'vars', c.nv, 'clauses', len(c.cls), flush=True)
st, model, dt = run.solve(a.out, a.timeout)
print(st, '%.1fs' % dt, flush=True)
if st == 'SATISFIABLE':
    fm = gen.decode(model, info, 15)
    print(gen.show(fm))
