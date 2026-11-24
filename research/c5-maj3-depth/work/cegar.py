#!/usr/bin/env python3
"""Row-CEGAR for the depth-D formula problem, incremental CaDiCaL (pysat).
Formula variables (t, s) and SB are built once; row constraints are added as rows are needed."""
import sys, os, time, random, argparse, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from pysat.solvers import Solver

class Inc:
    def __init__(self, sp, D, sb_swap='ts', sb_var=4, enc='kw', solver='cadical195', prec=True, refl=True):
        self.sp = sp; self.D = D; n = sp['n']
        c, info = gen.build(sp, D, [], [], sb_swap=sb_swap, sb_var=sb_var, enc=enc, sb_prec=prec, sb_refl=refl)
        self.c = c; self.info = info
        self.S = Solver(name=solver, bootstrap_with=c.cls)
        self.nclauses = len(c.cls)
        self.enc = enc
        self.rows = []
        self.NI = info['NI']; self.NL = info['NL']

    def add_row(self, side, r):
        sp = self.sp; n = sp['n']; NI, NL = self.NI, self.NL
        t, s = self.info['t'], self.info['s']
        c = self.c; start = len(c.cls)
        x = {k: c.new() for k in range(1, NI + NL + 1)}
        if side == 'a':
            O = sp['A'][r]
            c.add([x[1]])
            for k in range(1, NI + 1):
                L, R = 2 * k, 2 * k + 1
                c.add([-x[k], -t[k], x[L]]); c.add([-x[k], -t[k], x[R]]); c.add([-x[k], t[k], x[L], x[R]])
            for l in range(NI + 1, NI + NL + 1):
                c.add([-x[l]] + [s[l, v] for v in range(n) if O >> v & 1])
                for v in range(n):
                    if not O >> v & 1:
                        c.add([-x[l], -s[l, v]])
        else:
            O = sp['B'][r]
            c.add([x[1]])
            for k in range(1, NI + 1):
                L, R = 2 * k, 2 * k + 1
                c.add([-x[k], t[k], x[L]]); c.add([-x[k], t[k], x[R]]); c.add([-x[k], -t[k], x[L], x[R]])
            for l in range(NI + 1, NI + NL + 1):
                c.add([-x[l]] + [s[l, v] for v in range(n) if not O >> v & 1])
                for v in range(n):
                    if O >> v & 1:
                        c.add([-x[l], -s[l, v]])
        for cl in c.cls[start:]:
            self.S.add_clause(cl)
        self.rows.append((side, r))

    def solve(self, assumptions=()):
        r = self.S.solve(assumptions=list(assumptions))
        if not r:
            return None
        return gen.decode(self.S.get_model(), self.info, self.sp['n'])

def cegar(sp, D, cube=None, sb_var=4, seed=0, A=None, B=None, log=print, init=None, batch=1, tlimit=None, prec=True, refl=True):
    rng = random.Random(seed)
    A = list(range(len(sp['A']))) if A is None else A
    B = list(range(len(sp['B']))) if B is None else B
    inc = Inc(sp, D, sb_var=sb_var, prec=prec, refl=refl)
    t = inc.info['t']
    assum = [t[k] if v else -t[k] for k, v in (cube or {}).items()]
    have = set()
    for side, r in (init or [('a', rng.choice(A)), ('b', rng.choice(B))]):
        inc.add_row(side, r); have.add((side, r))
    t0 = time.time(); it = 0
    while True:
        it += 1
        t1 = time.time()
        fm = inc.solve(assum)
        na = sum(1 for x in have if x[0] == 'a'); nb = len(have) - na
        if fm is None:
            log('iter %d rows %d+%d UNSAT %.1fs (total %.1fs)' % (it, na, nb, time.time() - t1, time.time() - t0))
            return None, inc.rows
        badA = [r for r in A if not gen.ev(fm, sp['A'][r])]
        badB = [r for r in B if gen.ev(fm, sp['B'][r])]
        log('iter %d rows %d+%d SAT %.1fs bad %d+%d' % (it, na, nb, time.time() - t1, len(badA), len(badB)))
        if not badA and not badB:
            return fm, inc.rows
        for _ in range(batch):
            if badA:
                r = rng.choice(badA); badA.remove(r); inc.add_row('a', r); have.add(('a', r))
            if badB:
                r = rng.choice(badB); badB.remove(r); inc.add_row('b', r); have.add(('b', r))
        if tlimit and time.time() - t0 > tlimit:
            log('time limit'); return 'TIMEOUT', inc.rows

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--fn', default='c5'); ap.add_argument('--D', type=int, default=6)
    ap.add_argument('--cube', default=''); ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--sbvar', type=int, default=4); ap.add_argument('--batch', type=int, default=1)
    ap.add_argument('--tlimit', type=float, default=None); ap.add_argument('--save', default='')
    ap.add_argument('--prec', type=int, default=1); ap.add_argument('--refl', type=int, default=1)
    a = ap.parse_args()
    sp = gen.spec(a.fn)
    cube = {i + 1: int(ch) for i, ch in enumerate(a.cube) if ch in '01'}
    fm, rows = cegar(sp, a.D, cube=cube, sb_var=a.sbvar, seed=a.seed, batch=a.batch, tlimit=a.tlimit, prec=bool(a.prec), refl=bool(a.refl),
                     log=lambda m: print(m, flush=True))
    if fm is None:
        print('UNSAT core rows', len(rows))
    elif fm == 'TIMEOUT':
        print('TIMEOUT')
    else:
        ok = all(gen.ev(fm, x) == sp['tt'][x] for x in range(1 << sp['n']))
        print('FOUND depth', gen.depth(fm), 'correct', ok)
        print(gen.show(fm))
    if a.save:
        json.dump(dict(cube=a.cube, rows=rows, result=('UNSAT' if fm is None else ('TIMEOUT' if fm == 'TIMEOUT' else gen.show(fm)))), open(a.save, 'w'))
