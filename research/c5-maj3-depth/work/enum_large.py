#!/usr/bin/env python3
"""Enumerate, up to the symmetry group G, the minterm sets S (|S| >= k) accepted by depth-D
formulas that reject every Bob row (side a), or the Bob-row sets Z (|Z| >= k) rejected by
depth-D formulas accepting every minterm (side b). Each found set is blocked together with all
its G-images ('accept/reject something outside sigma(S)'). Ends when UNSAT: then every such set
is contained in a G-image of a listed one."""
import sys, os, time, json, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from rootsplit import group_perms, apply_mask
from pysat.solvers import Solver

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--D', type=int, default=5); ap.add_argument('--side', default='a')
    ap.add_argument('--k', type=int, required=True); ap.add_argument('--out', required=True)
    ap.add_argument('--kmax', type=int, required=True)
    ap.add_argument('--seed', default='')
    ap.add_argument('--cube', default='')  # json list of sets to list (and block) first
    a = ap.parse_args()
    sp = gen.spec('c5')
    G = group_perms(sp)
    rows = sp['A'] if a.side == 'a' else sp['B']
    idx = {t: r for r, t in enumerate(rows)}
    act = [[idx[apply_mask(p, t)] for t in rows] for p in G]
    ar = list(range(len(sp['A']))); br = list(range(len(sp['B'])))
    c, info = gen.build(sp, a.D, ar, br, sb_swap='ts', sb_var=4, sb_prec=True, sb_refl=True,
                        free_side=a.side, atleast_k=-a.kmax,
                        cube={i + 1: int(ch) for i, ch in enumerate(a.cube) if ch in '01'})
    counter = info['counter']
    rootlit = lambda side, r: info['root'][r]
    S = Solver(name='cadical195', bootstrap_with=c.cls)
    found = []; blocked = set(); t0 = time.time()
    def block(Sset):
        new = 0
        for pr in act:
            img = frozenset(pr[r] for r in Sset)
            if img in blocked:
                continue
            blocked.add(img); new += 1
            S.add_clause([rootlit(a.side, r) for r in range(len(rows)) if r not in img])
        return new
    if a.seed:
        for Sset in json.loads(open(a.seed).read()):
            found.append(dict(set=sorted(Sset), formula='seed', k=None))
            new = block(Sset)
            print('seed set size %d +%d blocked images' % (len(Sset), new), flush=True)
    kk = a.kmax
    while True:
        t1 = time.time()
        ok = S.solve(assumptions=[counter[kk]])
        if not ok:
            print('k=%d exhausted (%.1fs); %d sets so far, %.0fs' % (kk, time.time() - t1, len(found), time.time() - t0), flush=True)
            if kk <= a.k:
                print('DONE', flush=True)
                break
            kk -= 1
            continue
        fm = gen.decode(S.get_model(), info, sp['n'])
        if a.side == 'a':
            assert all(not gen.ev(fm, t) for t in sp['B'])
            Sset = [r for r, t in enumerate(sp['A']) if gen.ev(fm, t)]
        else:
            assert all(gen.ev(fm, t) for t in sp['A'])
            Sset = [r for r, t in enumerate(sp['B']) if not gen.ev(fm, t)]
        found.append(dict(set=Sset, formula=gen.show(fm), k=kk))
        new = block(Sset)
        print('set %d size %d (%.1fs) +%d blocked images, total %d' % (len(found), len(Sset), time.time() - t1, new, len(blocked)), flush=True)
        json.dump(dict(side=a.side, k=a.k, D=a.D, cube=a.cube, sets=found), open(a.out, 'w'))
    json.dump(dict(side=a.side, k=a.k, D=a.D, cube=a.cube, sets=found, complete=True), open(a.out, 'w'))

if __name__ == '__main__':
    main()
