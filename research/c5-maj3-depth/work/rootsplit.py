#!/usr/bin/env python3
"""Root-split CEGAR. A depth-6 formula has root OR (Alice/minterms split into two depth-5
solvable classes) or root AND (Bob/max-false rows split). Hard sets H (row sets on the split
side, with a set of rows on the other side, that no depth-5 formula separates) forbid
monochromatic G-images in the 2-colouring. Depth-5 checks: one incremental CaDiCaL with every
row guarded by a selector literal; swap symmetry breaking only."""
import sys, os, time, json, itertools, argparse, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
from pysat.solvers import Solver

def group_perms(sp):
    nb = sp['nb']; n = sp['n']
    perms = []
    for d in sp['bperms']:
        for ls in itertools.product(list(itertools.permutations(range(3))), repeat=nb):
            p = [0] * n
            for b in range(nb):
                for l in range(3):
                    p[b + nb * l] = d[b] + nb * ls[b][l]
            perms.append(p)
    return perms

def apply_mask(p, t):
    r = 0
    while t:
        v = (t & -t).bit_length() - 1
        t &= t - 1
        r |= 1 << p[v]
    return r

class Sel:
    def __init__(self, sp, D):
        self.sp = sp; n = sp['n']
        c, info = gen.build(sp, D, [], [], sb_swap='ts', sb_var=0)
        self.c = c; self.info = info
        NI, NL = info['NI'], info['NL']; t, s = info['t'], info['s']
        self.sel = {}
        for side, rows in (('a', sp['A']), ('b', sp['B'])):
            for r, O in enumerate(rows):
                g = c.new(); self.sel[side, r] = g
                x = {k: c.new() for k in range(1, NI + NL + 1)}
                c.add([-g, x[1]])
                for k in range(1, NI + 1):
                    L, R = 2 * k, 2 * k + 1
                    if side == 'a':
                        c.add([-x[k], -t[k], x[L]]); c.add([-x[k], -t[k], x[R]]); c.add([-x[k], t[k], x[L], x[R]])
                    else:
                        c.add([-x[k], t[k], x[L]]); c.add([-x[k], t[k], x[R]]); c.add([-x[k], -t[k], x[L], x[R]])
                for l in range(NI + 1, NI + NL + 1):
                    good = [v for v in range(n) if (O >> v & 1) == (1 if side == 'a' else 0)]
                    c.add([-x[l]] + [s[l, v] for v in good])
                    for v in range(n):
                        if v not in good:
                            c.add([-x[l], -s[l, v]])
        self.S = Solver(name='cadical195', bootstrap_with=c.cls)
        self.calls = 0
        self.verbose = False

    def check(self, rows):
        """rows: list of (side, r). Returns formula or None (then self.core = core rows)."""
        self.calls += 1
        ok = self.S.solve(assumptions=[self.sel[x] for x in rows])
        if ok:
            return gen.decode(self.S.get_model(), self.info, self.sp['n'])
        inv = {v: k for k, v in self.sel.items()}
        self.core = [inv[l] for l in self.S.get_core()]
        return None

    def check_cegar(self, rows, rng, init=4, add=2):
        """row-CEGAR inside the selector solver; same contract as check."""
        rows = list(rows)
        byside = {'a': [x for x in rows if x[0] == 'a'], 'b': [x for x in rows if x[0] == 'b']}
        act = set()
        for sd in 'ab':
            for x in rng.sample(byside[sd], min(init, len(byside[sd]))):
                act.add(x)
        sp = self.sp
        while True:
            t1 = time.time()
            fm = self.check(sorted(act))
            if self.verbose:
                print('   cegar %d rows %.1fs %s' % (len(act), time.time() - t1, 'sat' if fm else 'UNSAT'), flush=True)
            if fm is None:
                return None
            bad = {'a': [x for x in byside['a'] if not gen.ev(fm, sp['A'][x[1]])],
                   'b': [x for x in byside['b'] if gen.ev(fm, sp['B'][x[1]])]}
            if not bad['a'] and not bad['b']:
                return fm
            for sd in 'ab':
                for x in rng.sample(bad[sd], min(add, len(bad[sd]))):
                    act.add(x)

    def minimize(self, core, keep_side=None, log=None):
        """deletion-based core minimisation (rows on keep_side are tried first)."""
        core = list(core)
        order = sorted(core, key=lambda x: (x[0] != keep_side, random.random()))
        i = 0
        cur = set(core)
        for x in order:
            if x not in cur:
                continue
            trial = [y for y in cur if y != x]
            r = self.check(trial)
            if r is None:
                cur = set(self.core)
        return sorted(cur)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--fn', default='c5'); ap.add_argument('--D', type=int, default=6)
    ap.add_argument('--root', default='or', choices=['or', 'and'])
    ap.add_argument('--seed', type=int, default=0); ap.add_argument('--state', default='')
    ap.add_argument('--minimize', type=int, default=0)
    a = ap.parse_args()
    random.seed(a.seed); rng = random.Random(a.seed)
    sp = gen.spec(a.fn)
    G = group_perms(sp)
    split_side = 'a' if a.root == 'or' else 'b'
    other = 'b' if split_side == 'a' else 'a'
    rows = {'a': sp['A'], 'b': sp['B']}
    idx = {side: {t: r for r, t in enumerate(rows[side])} for side in 'ab'}
    # permutation action of G on the split side's rows
    act = [[idx[split_side][apply_mask(p, t)] for t in rows[split_side]] for p in G]
    NS = len(rows[split_side])
    print('group', len(G), 'split side', split_side, NS, flush=True)
    sel = Sel(sp, a.D - 1)
    sel.verbose = True
    print('depth-%d selector solver built: %d vars %d clauses' % (a.D - 1, sel.c.nv, len(sel.c.cls)), flush=True)
    hard = []  # list of (H split-side rows, H other-side rows)
    if a.state and os.path.exists(a.state):
        hard = [(tuple(h[0]), tuple(h[1])) for h in json.load(open(a.state))['hard']]
    col = Solver(name='cadical195')
    edges = set()
    def add_orbit(H):
        new = 0
        for pr in act:
            img = frozenset(pr[r] for r in H)
            if img not in edges:
                edges.add(img); new += 1
                col.add_clause([r + 1 for r in img]); col.add_clause([-(r + 1) for r in img])
        return new
    col.add_clause([1])
    for H in hard:
        add_orbit(H[0])
    it = 0; t0 = time.time()
    allother = [(other, r) for r in range(len(rows[other]))]
    while True:
        it += 1
        col.set_phases([(r + 1) * rng.choice((1, -1)) for r in range(NS)])
        if not col.solve():
            print('COLOURING UNSAT: root %s impossible; hard sets %d, hyperedges %d, %.0fs' % (a.root, len(hard), len(edges), time.time() - t0), flush=True)
            break
        m = col.get_model()
        pos = set(x for x in m if x > 0)
        S1 = [r for r in range(NS) if (r + 1) in pos]; S2 = [r for r in range(NS) if (r + 1) not in pos]
        res = []
        for S in (S1, S2):
            t1 = time.time()
            fm = sel.check_cegar([(split_side, r) for r in S] + allother, rng)
            res.append((S, fm, time.time() - t1))
        msg = 'iter %d |S1|=%d |S2|=%d ' % (it, len(S1), len(S2)) + ' '.join('%s(%.1fs)' % ('sat' if fm else 'UNSAT', dt) for S, fm, dt in res)
        if all(fm for S, fm, dt in res):
            print(msg, flush=True)
            fA, fB = res[0][1], res[1][1]
            fm = ('or' if a.root == 'or' else 'and', fA, fB)
            ok = all(gen.ev(fm, x) == sp['tt'][x] for x in range(1 << sp['n']))
            print('FOUND depth', gen.depth(fm), 'correct on all inputs', ok)
            print(gen.show(fm), flush=True)
            json.dump(dict(formula=gen.show(fm), hard=hard), open(a.state or 'found.json', 'w'))
            return
        for S, fm, dt in res:
            if fm is None:
                core = sel.core
                if a.minimize:
                    t1 = time.time()
                    core = sel.minimize(core, keep_side=split_side)
                    dtm = time.time() - t1
                else:
                    dtm = 0
                H = tuple(sorted(r for s_, r in core if s_ == split_side))
                Ho = tuple(sorted(r for s_, r in core if s_ == other))
                hard.append((H, Ho))
                new = add_orbit(H)
                msg += ' | hard %d+%d (min %.1fs) +%d edges' % (len(H), len(Ho), dtm, new)
        print(msg + ' total %d edges %.0fs' % (len(edges), time.time() - t0), flush=True)
        if a.state:
            json.dump(dict(hard=hard), open(a.state, 'w'))

if __name__ == '__main__':
    main()
