#!/usr/bin/env python3
"""Find a small row core (H_A subset of A_set, H_B subset of B) that no depth-D formula separates,
by row-CEGAR in an incremental CaDiCaL with selector literals; then shrink by deletion.
usage: core.py --aset JSON --out core.json [--shrink 1]"""
import sys, os, json, time, random, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from rootsplit import Sel
ap = argparse.ArgumentParser(); ap.add_argument('--D', type=int, default=5)
ap.add_argument('--aset', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--shrink', type=int, default=1); ap.add_argument('--seed', type=int, default=1)
a = ap.parse_args()
sp = gen.spec('c5'); rng = random.Random(a.seed)
Aset = json.loads(open(a.aset).read()) if os.path.exists(a.aset) else json.loads(a.aset)
sel = Sel(sp, a.D); sel.verbose = True
rows = [('a', r) for r in Aset] + [('b', r) for r in range(135)]
t0 = time.time()
fm = sel.check_cegar(rows, rng, init=4, add=2)
if fm is not None:
    print('SEPARABLE:', gen.show(fm)); json.dump(dict(separable=gen.show(fm)), open(a.out, 'w')); sys.exit(0)
core = sorted(sel.core)
print('core %d+%d after %.0fs' % (sum(1 for x in core if x[0] == 'a'), sum(1 for x in core if x[0] == 'b'), time.time() - t0), flush=True)
json.dump(dict(core=core), open(a.out, 'w'))
if a.shrink:
    cur = list(core)
    for x in sorted(core, key=lambda x: (x[0] != 'a', rng.random())):
        if x not in cur: continue
        trial = [y for y in cur if y != x]
        t1 = time.time()
        r = sel.check(trial)
        if r is None:
            cur = sorted(sel.core)
        print('  drop %s: %s (%.1fs) -> %d+%d' % (x, 'kept-out' if r is None else 'needed', time.time() - t1,
              sum(1 for y in cur if y[0] == 'a'), sum(1 for y in cur if y[0] == 'b')), flush=True)
        json.dump(dict(core=cur), open(a.out, 'w'))
    print('final core %d+%d %.0fs' % (sum(1 for y in cur if y[0] == 'a'), sum(1 for y in cur if y[0] == 'b'), time.time() - t0), flush=True)
