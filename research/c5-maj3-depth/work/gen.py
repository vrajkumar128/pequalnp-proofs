#!/usr/bin/env python3
"""CNF for: monotone fan-in-2 AND/OR formula of depth <= D (complete binary tree) computing
G o MAJ3 (G = C5 or P4), via a one-sided (Karchmer-Wigderson) encoding on the minterms and
maximal false points. Symmetry breaking: lex-leader constraints (one global variable order)
for the child swaps and for the variable group (block automorphisms x S3 per block)."""
import sys, itertools, json, argparse

def spec(name):
    if name == 'c5':
        nb = 5; edges = [(i, (i + 1) % 5) for i in range(5)]
        bperms = []
        for r in range(5):
            bperms.append([(b + r) % 5 for b in range(5)])
            bperms.append([(r - b) % 5 for b in range(5)])
    elif name == 'p4':
        nb = 4; edges = [(0, 1), (1, 2), (2, 3)]
        bperms = [[0, 1, 2, 3], [3, 2, 1, 0]]
    else:
        raise ValueError(name)
    n = 3 * nb
    blk = lambda b: [b, b + nb, b + 2 * nb]
    def F(t):
        m = [((t >> b) & 1) + ((t >> (b + nb)) & 1) + ((t >> (b + 2 * nb)) & 1) >= 2 for b in range(nb)]
        return any(m[u] and m[v] for u, v in edges)
    tt = [F(t) for t in range(1 << n)]
    mins = [t for t in range(1 << n) if tt[t] and all(not tt[t & ~(1 << i)] for i in range(n) if t >> i & 1)]
    maxf = [t for t in range(1 << n) if not tt[t] and all(tt[t | (1 << i)] for i in range(n) if not t >> i & 1)]
    return dict(name=name, nb=nb, n=n, edges=edges, bperms=bperms, F=F, tt=tt, A=mins, B=maxf)

def canon_min(seq, sp):
    """lex-min image of a sequence of variable indices under (block perms) x S3^nb."""
    nb = sp['nb']; best = None
    for d in sp['bperms']:
        lay = {}
        img = []
        for v in seq:
            b, l = v % nb, v // nb
            mp = lay.setdefault(b, {})
            if l not in mp:
                mp[l] = len(mp)
            img.append(d[b] + nb * mp[l])
        img = tuple(img)
        if best is None or img < best:
            best = img
    return best

class CNF:
    def __init__(self):
        self.nv = 0; self.cls = []
    def new(self):
        self.nv += 1; return self.nv
    def add(self, c):
        self.cls.append(c)
    def lex_ge(self, A, B):
        """A >=_lex B (lists of literals, same length); one-directional prefix-equality aux."""
        e = None
        for i, (x, y) in enumerate(zip(A, B)):
            pre = [] if e is None else [-e]
            self.add(pre + [x, -y])
            if i < len(A) - 1:
                e2 = self.new()
                self.add(pre + [-x, -y, e2])
                self.add(pre + [x, y, e2])
                e = e2

def atleast(c, lits, k, assert_it=True):
    """sequential counter: at least k of lits true. r[i][j] -> 'at least j of lits[0..i] true'
    (only the direction needed: r[i][j] implies the count, and r[n-1][k] is asserted)."""
    n = len(lits)
    prev = None
    for i in range(n):
        cur = {}
        for j in range(1, min(k, i + 1) + 1):
            v = c.new(); cur[j] = v
            # v -> (prev[j]) or (lits[i] and prev[j-1])
            opts = []
            if prev is not None and j in prev:
                opts.append(prev[j])
            if j == 1:
                # v -> prev[1] or lits[i]
                c.add([-v] + opts + [lits[i]])
            else:
                if prev is not None and (j - 1) in prev:
                    a = c.new()  # a <-> lits[i] and prev[j-1] (only a -> both needed)
                    c.add([-a, lits[i]]); c.add([-a, prev[j - 1]])
                    c.add([-v] + opts + [a])
                else:
                    c.add([-v] + opts)
        prev = cur
    if assert_it:
        c.add([prev[k]])
    return prev

def build(sp, D, arows, brows, sb_swap='ts', sb_rows=0, sb_var=4, cube=None, amo=True, enc='kw', sb_prec=False, sb_refl=False, lexperms=None, free_side=None, atleast_k=0, subgroup=None, sub_prefix=4):
    n = sp['n']; NI = (1 << D) - 1; NL = 1 << D
    c = CNF()
    t = {k: c.new() for k in range(1, NI + 1)}
    s = {(l, v): c.new() for l in range(NI + 1, NI + NL + 1) for v in range(n)}
    for l in range(NI + 1, NI + NL + 1):
        c.add([s[l, v] for v in range(n)])
        if amo:
            for v in range(n):
                for w in range(v + 1, n):
                    c.add([-s[l, v], -s[l, w]])
    A = sp['A']; B = sp['B']
    av = {}; bv = {}
    if enc == 'fun':
        rows = [(A[r], 1, ('a', r)) for r in arows] + [(B[r], 0, ('b', r)) for r in brows]
        for O, val, key in rows:
            x = {}
            for k in range(1, NI + NL + 1):
                x[k] = c.new()
                (av if key[0] == 'a' else bv)[k, key[1]] = x[k]
            c.add([x[1] if val else -x[1]])
            for k in range(1, NI + 1):
                L, R = 2 * k, 2 * k + 1
                c.add([-t[k], -x[k], x[L]]); c.add([-t[k], -x[k], x[R]]); c.add([-t[k], x[k], -x[L], -x[R]])
                c.add([t[k], x[k], -x[L]]); c.add([t[k], x[k], -x[R]]); c.add([t[k], -x[k], x[L], x[R]])
            for l in range(NI + 1, NI + NL + 1):
                c.add([-x[l]] + [s[l, v] for v in range(n) if O >> v & 1])
                c.add([x[l]] + [s[l, v] for v in range(n) if not O >> v & 1])
                for v in range(n):
                    c.add([-s[l, v], x[l] if O >> v & 1 else -x[l]])
        arows_, brows_ = arows, brows
        arows, brows = [], []
    for r in arows:
        for k in range(1, NI + NL + 1):
            av[k, r] = c.new()
    for r in brows:
        for k in range(1, NI + NL + 1):
            bv[k, r] = c.new()
    for r in arows:
        x = av
        if free_side not in ('a', 'ab'):
            c.add([x[1, r]])
        for k in range(1, NI + 1):
            L, R = 2 * k, 2 * k + 1
            c.add([-x[k, r], -t[k], x[L, r]]); c.add([-x[k, r], -t[k], x[R, r]])
            c.add([-x[k, r], t[k], x[L, r], x[R, r]])
        O = A[r]
        for l in range(NI + 1, NI + NL + 1):
            c.add([-x[l, r]] + [s[l, v] for v in range(n) if O >> v & 1])
            for v in range(n):
                if not O >> v & 1:
                    c.add([-x[l, r], -s[l, v]])
    for r in brows:
        x = bv
        if free_side not in ('b', 'ab'):
            c.add([x[1, r]])
        for k in range(1, NI + 1):
            L, R = 2 * k, 2 * k + 1
            c.add([-x[k, r], t[k], x[L, r]]); c.add([-x[k, r], t[k], x[R, r]])
            c.add([-x[k, r], -t[k], x[L, r], x[R, r]])
        O = B[r]
        for l in range(NI + 1, NI + NL + 1):
            c.add([-x[l, r]] + [s[l, v] for v in range(n) if not O >> v & 1])
            for v in range(n):
                if O >> v & 1:
                    c.add([-x[l, r], -s[l, v]])
    if free_side == 'ab':
        info_counter = (atleast(c, [av[1, r] for r in arows], atleast_k[0]),
                        atleast(c, [bv[1, r] for r in brows], atleast_k[1]))
    elif free_side:
        lits = [av[1, r] for r in arows] if free_side == 'a' else [bv[1, r] for r in brows]
        info_counter = atleast(c, lits, abs(atleast_k), assert_it=atleast_k > 0)
    nbase = len(c.cls)
    if enc == 'fun':
        arows, brows = arows_, brows_
    # --- swap symmetry breaking: for every internal node k, (subtree 2k) >=_lex (subtree 2k+1)
    # in the global order  t(BFS) , s(leaf, var) , rows (row order: arows then brows as given, nodes BFS)
    def sub_nodes(k):
        lv = [[k]]
        while lv[-1][0] <= NI:
            lv.append([2 * u + w for u in lv[-1] for w in (0, 1)])
        return lv
    if sb_swap:
        for k in range(1, NI + 1):
            L, R = sub_nodes(2 * k), sub_nodes(2 * k + 1)
            VA, VB = [], []
            for la, lb in zip(L, R):
                for u, w in zip(la, lb):
                    if u <= NI:
                        VA.append(t[u]); VB.append(t[w])
            if 's' in sb_swap:
                for u, w in zip(L[-1], R[-1]):
                    for v in range(n):
                        VA.append(s[u, v]); VB.append(s[w, v])
            if sb_rows:
                order = [('a', r) for r in arows] + [('b', r) for r in brows]
                for side, r in order[:sb_rows]:
                    x = av if side == 'a' else bv
                    for la, lb in zip(L, R):
                        for u, w in zip(la, lb):
                            VA.append(x[u, r]); VB.append(x[w, r])
            c.lex_ge(VA, VB)
    # --- variable-group symmetry breaking: the selections of the first sb_var leaves form the
    # lex-min (by variable index) sequence of their orbit.
    nvarcl = 0
    if sb_var:
        leaves = list(range(NI + 1, NI + 1 + sb_var))
        canon = [()]
        for ell in range(1, sb_var + 1):
            nxt = []
            for pre in canon:
                for v in range(n):
                    seq = pre + (v,)
                    if canon_min(seq, sp) == seq:
                        nxt.append(seq)
                    else:
                        c.add([-s[leaves[i], seq[i]] for i in range(ell)]); nvarcl += 1
            canon = nxt
    if sb_prec:
        # S3 value precedence in every block over the whole leaf sequence (lex-leader for the
        # transpositions of layers inside one block): var b+5 first occurs after var b, and
        # var b+10 first occurs after var b+5.
        nb = sp['nb']
        leaves = list(range(NI + 1, NI + NL + 1))
        pref = {}
        for v in range(n):
            prev = None
            for l in leaves:
                p_ = c.new()
                c.add([-s[l, v], p_])
                if prev is not None:
                    c.add([-prev, p_])
                # p_ -> s[l,v] or prev   (exactness not needed for soundness; keeps it tight)
                c.add([-p_, s[l, v]] + ([prev] if prev is not None else []))
                pref[l, v] = p_; prev = p_
        for b in range(nb):
            for lo, hi in ((b, b + nb), (b + nb, b + 2 * nb)):
                for i, l in enumerate(leaves):
                    if i == 0:
                        c.add([-s[l, hi]])
                    else:
                        c.add([-s[l, hi], pref[leaves[i - 1], lo]])
    if sb_refl:
        # lex-leader for each pure block permutation (layers fixed) over the whole s-block
        leaves = list(range(NI + 1, NI + NL + 1))
        nb = sp['nb']
        for d in sp['bperms']:
            if d == list(range(nb)):
                continue
            pv = [b + nb * l for l in range(3) for b in range(nb)]
            perm = {v: d[v % nb] + nb * (v // nb) for v in range(n)}
            # x >=_lex pi(x): position (l,v) of pi(x) holds x at (l, pi^-1(v))
            inv = {perm[v]: v for v in range(n)}
            VA = [s[l, v] for l in leaves for v in range(n)]
            VB = [s[l, inv[v]] for l in leaves for v in range(n)]
            c.lex_ge(VA, VB)
    if subgroup:
        # symmetry breaking for a subgroup H of the variable group (H preserves the row sets):
        # (1) the selections of the first leaves are lex-min in their H-orbit (brute force over H);
        # (2) value precedence for every single-block layer transposition in H;
        # (3) a full s-block lex constraint for every pure block permutation in H.
        nb = sp['nb']
        leaves = list(range(NI + 1, NI + NL + 1))
        Hs = [tuple(p) for p in subgroup]
        canon = [()]
        for ell in range(1, sub_prefix + 1):
            nxt = []
            for pre in canon:
                for v in range(n):
                    seq = pre + (v,)
                    if min(tuple(p[x] for x in seq) for p in Hs) == seq:
                        nxt.append(seq)
                    else:
                        c.add([-s[leaves[i], seq[i]] for i in range(ell)])
            canon = nxt
        idp = tuple(range(n))
        pref = None
        for p in Hs:
            moved = [v for v in range(n) if p[v] != v]
            if len(moved) == 2 and moved[0] % nb == moved[1] % nb:
                lo, hi = sorted(moved)
                if pref is None:
                    pref = {}
                    for v in range(n):
                        prev = None
                        for l in leaves:
                            q = c.new(); c.add([-s[l, v], q])
                            if prev is not None: c.add([-prev, q])
                            c.add([-q, s[l, v]] + ([prev] if prev is not None else []))
                            pref[l, v] = q; prev = q
                for i, l in enumerate(leaves):
                    c.add([-s[l, hi]] + ([pref[leaves[i - 1], lo]] if i else []))
            elif p != idp and all(p[v] // nb == v // nb for v in range(n)) and all(p[v] % nb == p[v % nb] % nb for v in range(n)):
                inv = {p[v]: v for v in range(n)}
                VA = [s[l, v] for l in leaves for v in range(n)]
                VB = [s[l, inv[v]] for l in leaves for v in range(n)]
                c.lex_ge(VA, VB)
    for perm in (lexperms or []):
        # x >=_lex pi(x) over the whole s-block, pi a variable permutation preserving the row set
        leaves = list(range(NI + 1, NI + NL + 1))
        inv = {perm[v]: v for v in range(n)}
        VA = [s[l, v] for l in leaves for v in range(n)]
        VB = [s[l, inv[v]] for l in leaves for v in range(n)]
        c.lex_ge(VA, VB)
    if cube:
        for k, val in cube.items():
            c.add([t[k] if val else -t[k]])
    info = dict(NI=NI, NL=NL, t=t, s=s, nbase=nbase, nvarcl=nvarcl)
    if free_side:
        info['counter'] = info_counter
        if free_side != 'ab':
            info['root'] = {r: (av[1, r] if free_side == 'a' else bv[1, r]) for r in (arows if free_side == 'a' else brows)}
    return c, info

def write(c, path, comments=()):
    with open(path, 'w') as f:
        for cm in comments:
            f.write('c %s\n' % cm)
        f.write('p cnf %d %d\n' % (c.nv, len(c.cls)))
        for cl in c.cls:
            f.write(' '.join(map(str, cl)) + ' 0\n')

def decode(model, info, n):
    m = set(x for x in model if x > 0)
    NI = info['NI']; t = info['t']; s = info['s']
    def rec(k):
        if k > NI:
            vs = [v for v in range(n) if s[k, v] in m]
            return ('x', vs[0])
        return ('and' if t[k] in m else 'or', rec(2 * k), rec(2 * k + 1))
    return rec(1)

def ev(fm, pt):
    if fm[0] == 'x':
        return pt >> fm[1] & 1
    a = ev(fm[1], pt); b = ev(fm[2], pt)
    return (a & b) if fm[0] == 'and' else (a | b)

def show(fm):
    if fm[0] == 'x':
        return 'z%d' % fm[1]
    return '(' + show(fm[1]) + (' && ' if fm[0] == 'and' else ' || ') + show(fm[2]) + ')'

def depth(fm):
    return 0 if fm[0] == 'x' else 1 + max(depth(fm[1]), depth(fm[2]))

def parse(sexpr):
    """parse the show() format back into a tree"""
    import re
    toks = re.findall(r'\(|\)|&&|\|\||z\d+', sexpr)
    pos = [0]
    def p():
        tk = toks[pos[0]]; pos[0] += 1
        if tk.startswith('z'):
            return ('x', int(tk[1:]))
        assert tk == '('
        l = p(); op = toks[pos[0]]; pos[0] += 1; r = p()
        assert toks[pos[0]] == ')'; pos[0] += 1
        return ('and' if op == '&&' else 'or', l, r)
    return p()
