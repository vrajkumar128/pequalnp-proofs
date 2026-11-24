#!/usr/bin/env python3
"""Sub-rectangle: Alice minterms with the same missing layer in both blocks, Bob rows with the
single one at the same layer in all three false blocks. Symmetry: D5 x diagonal S3."""
import sys, os, itertools, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen, run
ap = argparse.ArgumentParser(); ap.add_argument('--D', type=int, default=6); ap.add_argument('--out', default='aligned.cnf')
ap.add_argument('--mode', default='aligned'); ap.add_argument('--fn', default='c5')
a = ap.parse_args()
sp = gen.spec(a.fn); NB = sp['nb']; N = sp['n']
def layers(t, b):
    return [l for l in range(3) if t >> (b + NB * l) & 1]
ar = []
for r, t in enumerate(sp['A']):
    blocks = [b for b in range(5) if len(layers(t, b)) == 2]
    miss = set(({0, 1, 2} - set(layers(t, b))).pop() for b in blocks)
    if len(miss) == 1: ar.append(r)
br = []
for r, t in enumerate(sp['B']):
    blocks = [b for b in range(5) if len(layers(t, b)) == 1]
    q = set(layers(t, b)[0] for b in blocks)
    if len(q) == 1: br.append(r)
G = []
for d in sp['bperms']:
    for lp in itertools.permutations(range(3)):
        p = [d[v % 5] + 5 * lp[v // 5] for v in range(15)]
        if p != list(range(N)): G.append(p)
c, info = gen.build(sp, a.D, ar, br, sb_swap='ts', sb_var=0, lexperms=G)
gen.write(c, a.out)
print('rows', len(ar), len(br), 'perms', len(G), 'vars', c.nv, 'clauses', len(c.cls), flush=True)
st, model, dt = run.solve(a.out)
print(st, '%.1fs' % dt, flush=True)
if st == 'SATISFIABLE':
    fm = gen.decode(model, info, N)
    print('depth', gen.depth(fm), 'okA', all(gen.ev(fm, sp['A'][r]) for r in ar), 'okB', all(not gen.ev(fm, sp['B'][r]) for r in br))
    print(gen.show(fm))
