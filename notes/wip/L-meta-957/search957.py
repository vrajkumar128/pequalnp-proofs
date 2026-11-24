#!/usr/bin/env python3
"""L-meta-957: CEGIS exact synthesis of fan-in-2 AND/OR/NOT gate lists with at most K NOT gates
computing several outputs (here: the 13 line-ORs of PG(2,3), lines {0,1,3,9}+w mod 13).

Encoding = the circuit_synth NF encoding (A/B one-hot selectors with ladders, a <= b, a = b iff
NOT, op bit, per-row values) built incrementally in one CaDiCaL instance; rows are added by
counterexample-guided refinement. Symmetry breaking (sound for "<= s gates", see SOUNDNESS):
  order     greedy topological order, key (b, a, op) strictly increasing over all gate pairs
  distinct  each gate's row vector (on the CURRENT row set R) differs from every earlier wire
            and from both constants (re-posted under a fresh activation literal per iteration)
  (no 'used': instance at exactly s gates then covers every circuit with <= s gates)
SOUNDNESS of 'exactly s covers <= s': a circuit correct on R normalizes relative to R (constant
gates, duplicate gates, unused gates deleted; NOT count never grows) to s' <= s gates; R contains
all 78 pair rows, so the 78 functions AND(x_i, x_j) are pairwise distinct and non-constant on R;
pad with AND(x_i, x_j) gates whose row vector is new (exists while 78 > #wires), then re-sort
greedily: keys stay distinct, so the padded circuit is in the class with exactly s gates.
Every SAT model is decoded and re-evaluated with the exact Lean semantics on all 2^n inputs.

Case splits (extra constraints, each documented in the log): NOT gate at a fixed position p,
NOT reading a fixed wire, exact NOT count, fixed output positions, forbidding a NOT etc.
"""
import itertools, os, random, sys, time, json, hashlib, argparse
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

N13 = 13
DIFF = (0, 1, 3, 9)
LINES = [sorted({(u + w) % 13 for u in DIFF}) for w in range(13)]


def line_tables(n=13, lines=LINES):
    R = 1 << n
    tabs = []
    for L in lines:
        m = 0
        for t in range(R):
            if any((t >> i) & 1 for i in L):
                m |= 1 << t
        tabs.append(m)
    return tabs


def lean_wires(gates, x):
    w = list(x)
    for op, ins in gates:
        vals = [w[i] if 0 <= i < len(w) else False for i in ins]
        if op == 'and':
            r = all(vals)
        elif op == 'or':
            r = any(vals)
        elif op == 'not':
            r = not (vals[0] if vals else False)
        else:
            raise ValueError(op)
        w.append(r)
    return w


def bit_wires(n, gates):
    """Bit-parallel exact evaluation: wire value as an int over all 2^n inputs (bit t = row t)."""
    R = 1 << n
    full = (1 << R) - 1
    w = []
    for i in range(n):
        m = 0
        blk = (1 << (1 << i)) - 1  # pattern: bit t set iff bit i of t
        pat = ((1 << (1 << i)) - 1) << (1 << i)
        per = 1 << (i + 1)
        m = 0
        x = pat
        k = per
        while k < R:
            x |= x << k
            k <<= 1
        w.append(x & full)
    for op, ins in gates:
        vals = [w[i] if 0 <= i < len(w) else 0 for i in ins]
        if op == 'and':
            r = full
            for v in vals:
                r &= v
        elif op == 'or':
            r = 0
            for v in vals:
                r |= v
        else:
            r = full & ~(vals[0] if vals else 0)
        w.append(r)
    return w


class Enc:
    def __init__(self, n, tabs, s, maxnot=1, exact_not=None, sb_order=True, sb_distinct=True,
                 solver='cadical195', extra=None, lib=(), relevant=True):
        # lib: truth tables of fixed 'library' wires n..n+len(lib)-1 (cost 0, read freely)
        self.lib = list(lib)
        self.n0 = n
        n = n + len(self.lib)
        self.n, self.tabs, self.s = n, tabs, s
        self.maxnot = maxnot
        self.sb_distinct = sb_distinct
        self.nv = 0
        self.S = Solver(name=solver)
        self.nclauses = 0
        self.rows = []
        self.v = {j: [] for j in range(s)}
        self.dvars = {}   # (k, j) -> list of diff vars per row (k < j gates)
        self.act = None
        allow_not = maxnot > 0
        self.A, self.B, self.ulA, self.ulB, self.op, self.isnot = {}, {}, {}, {}, {}, {}
        for j in range(s):
            W = n + j
            self.A[j] = [self.var() for _ in range(W)]
            self.B[j] = [self.var() for _ in range(W)]
            self.ulA[j] = self.ladder(self.A[j])
            self.ulB[j] = self.ladder(self.B[j])
            self.op[j] = self.var()   # true = AND
            self.isnot[j] = self.var() if allow_not else None
            for w in range(W):
                self.add([-self.A[j][w], self.lit(self.ulB[j](w if allow_not else w + 1))])
                if allow_not:
                    self.add([-self.A[j][w], -self.B[j][w], self.isnot[j]])
                    self.add([-self.isnot[j], -self.A[j][w], self.B[j][w]])
            if allow_not:
                self.add([-self.isnot[j], -self.op[j]])
        if allow_not:
            nots = [self.isnot[j] for j in range(s)]
            cnf = CardEnc.atmost(lits=nots, bound=maxnot, top_id=self.nv, encoding=EncType.seqcounter)
            self.nv = max(self.nv, cnf.nv)
            for c in cnf.clauses:
                self.add(c)
            if exact_not is not None:
                cnf = CardEnc.atleast(lits=nots, bound=exact_not, top_id=self.nv, encoding=EncType.seqcounter)
                self.nv = max(self.nv, cnf.nv)
                for c in cnf.clauses:
                    self.add(c)
        # outputs: each output is some gate
        self.outsel = []
        for k in range(len(tabs)):
            sel = [self.var() for _ in range(s)]
            self.add(sel)
            self.outsel.append(sel)
        if sb_order:
            for p in range(s):
                for q in range(p + 1, s):
                    eqb, eqab = self.var(), self.var()
                    for beta in range(n + p):
                        self.add([-self.B[q][beta], self.lit(self.neg(self.ulB[p](beta + 1)))])
                        self.add([-self.B[q][beta], -self.B[p][beta], eqb])
                    for alpha in range(n + p):
                        self.add([-eqb, -self.A[q][alpha], self.lit(self.neg(self.ulA[p](alpha + 1)))])
                        self.add([-eqb, -self.A[q][alpha], -self.A[p][alpha], eqab])
                    self.add([-eqab, -self.op[p]])
                    self.add([-eqab, self.op[q]])
        # relevant: every input is read by some gate (all inputs matter; not with a library)
        if relevant and not self.lib:
            for i in range(n):
                dep = any(((tt >> t) & 1) != ((tt >> (t ^ (1 << i))) & 1)
                          for tt in tabs for t in range(1 << n))
                if dep:
                    self.add([X[j][i] for j in range(s) for X in (self.A, self.B)])
        if extra:
            extra(self)

    # --- helpers
    def var(self):
        self.nv += 1
        return self.nv

    @staticmethod
    def neg(l):
        if l is True:
            return False
        if l is False:
            return True
        return -l

    def lit(self, l):
        return l

    def add(self, cl):
        out = []
        for l in cl:
            if l is True:
                return
            if l is False:
                continue
            out.append(l)
        self.S.add_clause(out)
        self.nclauses += 1

    def ladder(self, X):
        m = len(X)
        U = [None] + [self.var() for _ in range(1, m)]

        def ul(i):
            if i <= 0:
                return True
            if i >= m:
                return False
            return U[i]
        for i in range(m):
            self.add([self.neg(ul(i)), ul(i + 1), X[i]])
            self.add([-X[i], ul(i)])
            self.add([-X[i], self.neg(ul(i + 1))])
            if i >= 1:
                self.add([self.neg(ul(i + 1)), ul(i)])
        return ul

    # --- rows
    def add_row(self, t):
        n, s = self.n, self.s
        x = [bool((t >> i) & 1) for i in range(self.n0)] + [bool((L >> t) & 1) for L in self.lib]
        r = len(self.rows)
        self.rows.append(t)

        def val(w):
            if w < n:
                return x[w]
            return self.v[w - n][r]
        for j in range(s):
            W = n + j
            g = self.var()
            self.v[j].append(g)
            xa, xb = self.var(), self.var()
            for w in range(W):
                xv = val(w)
                for X, y in ((self.A[j][w], xa), (self.B[j][w], xb)):
                    self.add([-X, self.neg(xv), y])
                    self.add([-X, xv, -y])
            o, tn = self.op[j], self.isnot[j]
            if tn is not None:
                self.add([-tn, g, xa])
                self.add([-tn, -g, -xa])
                T = [tn]
            else:
                T = []
            self.add(T + [-o, -g, xa])
            self.add(T + [-o, -g, xb])
            self.add(T + [-o, g, -xa, -xb])
            self.add(T + [o, g, -xa])
            self.add(T + [o, g, -xb])
            self.add(T + [o, -g, xa, xb])
        for k, tt in enumerate(self.tabs):
            want = (tt >> t) & 1
            for j in range(s):
                self.add([-self.outsel[k][j], self.v[j][r] if want else -self.v[j][r]])
        if self.sb_distinct:
            for j in range(s):
                for k in range(j):
                    d = self.var()
                    self.add([-d, self.v[k][r], self.v[j][r]])
                    self.add([-d, -self.v[k][r], -self.v[j][r]])
                    self.dvars.setdefault((k, j), []).append(d)

    def add_vrow(self, t, c):
        """Virtual row: input t evaluated with every NOT gate's value forced to the constant c
        (the C0 / C1 circuits). No correctness constraint. Returns per-gate value literals."""
        n, s = self.n, self.s
        x = [bool((t >> i) & 1) for i in range(self.n0)] + [bool((L >> t) & 1) for L in self.lib]
        vals = []

        def val(w):
            if w < n:
                return x[w]
            return vals[w - n]
        for j in range(s):
            W = n + j
            g = self.var()
            vals.append(g)
            xa, xb = self.var(), self.var()
            for w in range(W):
                xv = val(w)
                for X, y in ((self.A[j][w], xa), (self.B[j][w], xb)):
                    self.add([-X, self.neg(xv), y])
                    self.add([-X, xv, -y])
            o, tn = self.op[j], self.isnot[j]
            if tn is not None:
                self.add([-tn, g if c else -g])
                T = [tn]
            else:
                T = []
            self.add(T + [-o, -g, xa])
            self.add(T + [-o, -g, xb])
            self.add(T + [-o, g, -xa, -xb])
            self.add(T + [o, g, -xa])
            self.add(T + [o, g, -xb])
            self.add(T + [o, -g, xa, xb])
        return vals

    def out_lit(self, k, vals):
        """Literal equal to output k's value given per-gate value literals."""
        o = self.var()
        for j in range(self.s):
            self.add([-self.outsel[k][j], -vals[j], o])
            self.add([-self.outsel[k][j], vals[j], -o])
        return o

    def post_distinct(self):
        """(Re)post the distinctness constraints on the current row set under a new activation."""
        if not self.sb_distinct:
            return []
        a = self.var()
        R = len(self.rows)
        n = self.n
        X = [[bool((t >> i) & 1) for i in range(self.n0)] + [bool((L >> t) & 1) for L in self.lib]
             for t in self.rows]
        for j in range(self.s):
            self.add([-a] + [self.v[j][r] for r in range(R)])
            self.add([-a] + [-self.v[j][r] for r in range(R)])
            for w in range(n):
                self.add([-a] + [(-self.v[j][r] if X[r][w] else self.v[j][r]) for r in range(R)])
            for k in range(j):
                self.add([-a] + self.dvars[(k, j)])
        if self.act is not None:
            self.add([-self.act])   # retire the previous activation (its clauses become void)
        self.act = a
        return [a]

    def decode(self, model):
        ms = set(l for l in model if l > 0)
        n = self.n
        gates = []
        for j in range(self.s):
            a = [w for w, x in enumerate(self.A[j]) if x in ms]
            b = [w for w, x in enumerate(self.B[j]) if x in ms]
            assert len(a) == 1 and len(b) == 1
            a, b = a[0], b[0]
            if a == b:
                gates.append(('not', [a]))
            else:
                gates.append(('and' if self.op[j] in ms else 'or', [a, b]))
        outs = []
        for sel in self.outsel:
            js = [j for j, x in enumerate(sel) if x in ms]
            outs.append(n + js[0])
        return gates, outs


def bit_wires_lib(n, lib, gates):
    """Like bit_wires, with library wires n..n+len(lib)-1 given by their tables."""
    R = 1 << n
    full = (1 << R) - 1
    w = bit_wires(n, [])
    w = w + list(lib)
    for op, ins in gates:
        vals = [w[i] if 0 <= i < len(w) else 0 for i in ins]
        if op == 'and':
            r = full
            for v in vals:
                r &= v
        elif op == 'or':
            r = 0
            for v in vals:
                r |= v
        else:
            r = full & ~(vals[0] if vals else 0)
        w.append(r)
    return w


def check_all(n, tabs, gates, outs, maxnot, lib=()):
    """Exact check; returns list of (output k, wrong-row mask)."""
    assert all(op in ('and', 'or', 'not') and len(ins) <= 2 for op, ins in gates)
    assert sum(op == 'not' for op, _ in gates) <= maxnot
    W = bit_wires_lib(n, lib, gates) if lib else bit_wires(n, gates)
    bad = []
    for k, (tt, o) in enumerate(zip(tabs, outs)):
        val = W[o] if 0 <= o < len(W) else 0
        diff = val ^ tt
        if diff:
            bad.append((k, diff))
    return bad


def popcount(x):
    return bin(x).count('1')


def pick_cex(n, bad, per_out=2, rng=None):
    """Pick counterexample rows: for each wrong output, the wrong rows of least weight
    (ties broken by rng)."""
    rows = set()
    for k, diff in bad:
        cands = []
        t = diff
        while t:
            low = t & -t
            idx = low.bit_length() - 1
            cands.append(idx)
            t ^= low
        cands.sort(key=lambda r: (popcount(r), rng.random() if rng else 0))
        for r in cands[:per_out]:
            rows.add(r)
    return rows


def initial_rows(n, lines, extra_random=0, rng=None):
    rs = {0}
    for i in range(n):
        rs.add(1 << i)
    for i, j in itertools.combinations(range(n), 2):
        rs.add((1 << i) | (1 << j))
    full = (1 << n) - 1
    for L in lines:
        m = sum(1 << i for i in L)
        rs.add(m)
        rs.add(full & ~m)
    if rng:
        for _ in range(extra_random):
            rs.add(rng.randrange(1 << n))
    return rs


def cegis(n, tabs, lines, s, maxnot=1, exact_not=None, extra=None, log=print, time_limit=None,
          per_out=2, seed=1, sb_order=True, sb_distinct=True, init_rows=None, extra_random=20,
          max_iter=100000, lib=()):
    rng = random.Random(seed)
    t0 = time.time()
    E = Enc(n, tabs, s, maxnot, exact_not, sb_order, sb_distinct, extra=extra, lib=lib)
    rows = init_rows if init_rows is not None else initial_rows(n, lines, extra_random, rng)
    for t in sorted(rows):
        E.add_row(t)
    log('  enc: s=%d maxnot=%d rows=%d vars=%d clauses=%d build %.1fs' %
        (s, maxnot, len(E.rows), E.nv, E.nclauses, time.time() - t0))
    it = 0
    while it < max_iter:
        it += 1
        assum = E.post_distinct()
        ts = time.time()
        if time_limit is not None and time.time() - t0 > time_limit:
            log('  iter %d: TIMEOUT (time limit between iterations, rows %d)' % (it, len(E.rows)))
            return ('TIMEOUT', None, E, it)
        res = E.S.solve(assumptions=assum)   # CaDiCaL: no interrupt; long solves are bounded externally
        dt = time.time() - ts
        if res is None:
            log('  iter %d: TIMEOUT after %.1fs (rows %d)' % (it, dt, len(E.rows)))
            return ('TIMEOUT', None, E, it)
        if res is False:
            log('  iter %d: UNSAT %.1fs (rows %d) total %.1fs' % (it, dt, len(E.rows), time.time() - t0))
            return ('UNSAT', None, E, it)
        gates, outs = E.decode(E.S.get_model())
        bad = check_all(n, tabs, gates, outs, maxnot, lib)
        if not bad:
            log('  iter %d: SAT %.1fs, VERIFIED on all %d inputs (rows %d) total %.1fs' %
                (it, dt, 1 << n, len(E.rows), time.time() - t0))
            return ('SAT', (gates, outs), E, it)
        new = pick_cex(n, bad, per_out, rng) - set(E.rows)
        assert new, 'counterexample rows already present: encoding bug'
        for t in sorted(new):
            E.add_row(t)
        if it % 10 == 1 or dt > 20:
            log('  iter %d: SAT %.1fs, %d wrong outputs, +%d rows -> %d, vars %d clauses %d' %
                (it, dt, len(bad), len(new), len(E.rows), E.nv, E.nclauses))
    return ('ITERLIMIT', None, E, it)


def plain_circuit(lines=LINES, n=13):
    gates = []
    outs = []
    for L in lines:
        a, b, c, d = L
        gates.append(('or', [a, b]))
        gates.append(('or', [c, d]))
        gates.append(('or', [n + len(gates) - 2, n + len(gates) - 1]))
        outs.append(n + len(gates) - 1)
    return gates, outs



def deficit_constraints(lines=LINES, flag=(0, 0), min_total=2, n=13):
    """Necessary conditions for a one-NOT list with <= 38 gates (family bound, see notes):
    C1 = list with the NOT gate := true, C0 = := false (virtual rows). Line w is type 0 iff
    C1_w(m_w) = 1 (m_w = complement of the line); a deficit flag (w, u), u in L_w, is type 0
    with C0_w(e_u) = 0. s <= 38 forces at least min_total deficit flags; by flag-transitivity of
    PGL(3,3), (line 0, point 0) can be assumed to be one of them."""
    def extra(E):
        full = (1 << n) - 1
        t0 = {}
        for w, L in enumerate(lines):
            m = full & ~sum(1 << i for i in L)
            vals = E.add_vrow(m, 1)
            t0[w] = E.out_lit(w, vals)
        c0vals = {u: E.add_vrow(1 << u, 0) for u in range(n)}
        defs = {}
        for w, L in enumerate(lines):
            for u in L:
                c = E.out_lit(w, c0vals[u])
                d = E.var()
                E.add([-d, t0[w]])
                E.add([-d, -c])
                E.add([d, -t0[w], c])
                defs[(w, u)] = d
        if flag is not None:
            E.add([defs[flag]])
        lits = list(defs.values())
        cnf = CardEnc.atleast(lits=lits, bound=min_total, top_id=E.nv, encoding=EncType.seqcounter)
        E.nv = max(E.nv, cnf.nv)
        for c in cnf.clauses:
            E.add(c)
        E.defs = defs
        E.t0 = t0
    return extra



def family_constraints(lines=LINES, flag=(0, 0), min_total=2, n=13, bound=True, outidx=None,
                       famlines=None, perline=False):
    """deficit_constraints plus the whole family bound as one redundant cardinality constraint.
    THEOREM (re-derived in notes.md; L-meta-951's partial_bound): with C1 / C0 = the list with
    the NOT gate := true / false, P1, P0 = unit profiles, m_w = complement of line w,
      F1_w = {gates g : C1_g(m_w) = 0, |P1(g)| >= 2},  F0_w = {g : C0_g(m_w) = 0, |P0(g)| >= 2},
    type 1 (C1_w(m_w) = 0) lines have |F1_w| >= 3, type 0 lines |F0_w| >= (|A0(w)| - 1)^+ with
    A0(w) = P0(out_w), the families used are pairwise disjoint and the NOT gate is in none. Hence
      sum_w c_w + #(gates in no family) <= s,   c_w = |L_w| - 1 (type 1), (|A0(w)| - 1)^+ (type 0).
    Encoded with bits b_w^k (k = 1..|L_w|-1) forced true when c_w >= k, and inF_g allowed only for
    gates that are in some F1_w or F0_w:  sum b + sum (not inF) <= s."""
    def extra(E):
        full = (1 << n) - 1
        s = E.s
        oi = outidx or list(range(len(lines)))
        FL = [list(L) for L in (famlines or lines)]
        pos = [FL.index(list(L)) for L in lines]
        mrow = [full & ~sum(1 << i for i in L) for L in FL]
        pts = sorted(set(u for L in lines for u in L)) if not bound else list(range(n))
        v1m = [E.add_vrow(m, 1) for m in mrow]
        v0m = [E.add_vrow(m, 0) for m in mrow] if bound else None
        v0e = {u: E.add_vrow(1 << u, 0) for u in pts}
        v1e = {u: E.add_vrow(1 << u, 1) for u in range(n)} if bound else None
        t0 = [E.out_lit(oi[w], v1m[pos[w]]) for w in range(len(lines))]
        c0 = {}
        defs = {}
        for w, L in enumerate(lines):
            for u in L:
                c0[(w, u)] = E.out_lit(oi[w], v0e[u])
                d = E.var()
                E.add([-d, t0[w]])
                E.add([-d, -c0[(w, u)]])
                E.add([d, -t0[w], c0[(w, u)]])
                defs[(w, u)] = d
        if flag is not None:
            E.add([defs[flag]])
        if min_total:
            cnf = CardEnc.atleast(lits=list(defs.values()), bound=min_total, top_id=E.nv,
                                  encoding=EncType.seqcounter)
            E.nv = max(E.nv, cnf.nv)
            for c in cnf.clauses:
                E.add(c)
        E.defs, E.t0 = defs, t0
        if not bound:
            return
        bits = []
        for w, L in enumerate(lines):
            for k in range(1, len(L)):
                b = E.var()
                bits.append(b)
                E.add([t0[w], b])
                for T in itertools.combinations(L, k + 1):
                    E.add([-c0[(w, u)] for u in T] + [b])
        notin = []
        for j in range(s):
            big = []
            for vals in (v1e, v0e):
                bg = E.var()
                for u in range(n):
                    E.add([-bg] + [vals[u2][j] for u2 in range(n) if u2 != u])
                big.append(bg)
            inF, a1, a0 = E.var(), E.var(), E.var()
            E.add([-inF, a1, a0])
            E.add([-a1, big[0]])
            E.add([-a1] + [-v1m[w][j] for w in range(len(FL))])
            E.add([-a0, big[1]])
            E.add([-a0] + [-v0m[w][j] for w in range(len(FL))])
            notin.append(-inF)
        cnf = CardEnc.atmost(lits=bits + notin, bound=s, top_id=E.nv, encoding=EncType.totalizer)
        E.nv = max(E.nv, cnf.nv)
        for c in cnf.clauses:
            E.add(c)
        if not perline:
            return
        # per-line family sizes (implied by the same theorem), with exact family membership
        bigx = {}
        for j in range(s):
            for wi, vals in ((1, v1e), (0, v0e)):
                bg = E.var()
                for u, u2 in itertools.combinations(range(n), 2):
                    E.add([-vals[u][j], -vals[u2][j], bg])
                for u in range(n):
                    E.add([-bg] + [vals[u2][j] for u2 in range(n) if u2 != u])
                bigx[(j, wi)] = bg

        def atleast_if(lits, k, cond):
            # cond (list of literals, conjunction) -> at least k of lits
            cnf = CardEnc.atleast(lits=lits, bound=k, top_id=E.nv, encoding=EncType.seqcounter)
            E.nv = max(E.nv, cnf.nv)
            for c in cnf.clauses:
                E.add(c + [-x for x in cond])
        for w, L in enumerate(lines):
            f1, f0 = [], []
            for j in range(s):
                for wi, vm, fl in ((1, v1m, f1), (0, v0m, f0)):
                    f = E.var()
                    E.add([-f, -vm[pos[w]][j]])
                    E.add([-f, bigx[(j, wi)]])
                    E.add([f, vm[pos[w]][j], -bigx[(j, wi)]])
                    fl.append(f)
            atleast_if(f1, len(L) - 1, [-t0[w]])
            for k in range(1, len(L)):
                for T in itertools.combinations(L, k + 1):
                    atleast_if(f0, k, [t0[w]] + [c0[(w, u)] for u in T])
    return extra


# ---------------------------------------------------------------- PG(2,3) collineations

NPTS = 13
LSET = [frozenset(L) for L in LINES]
LINE_OF = {}
for w, L in enumerate(LSET):
    for a, b in itertools.combinations(sorted(L), 2):
        LINE_OF[(a, b)] = w
        LINE_OF[(b, a)] = w


def collinear(a, b, c):
    if a == b or b == c or a == c:
        return True
    return c in LSET[LINE_OF[(a, b)]]


def collineations():
    """All permutations of the 13 points mapping lines to lines (backtracking)."""
    out = []
    img = [None] * NPTS
    used = [False] * NPTS

    def ok(k):
        for a, b in itertools.combinations(range(k), 2):
            c = k
            if collinear(a, b, c) != collinear(img[a], img[b], img[c]):
                return False
        return True

    def rec(k):
        if k == NPTS:
            out.append(tuple(img))
            return
        for v in range(NPTS):
            if used[v]:
                continue
            img[k] = v
            if ok(k):
                used[v] = True
                rec(k + 1)
                used[v] = False
            img[k] = None
    rec(0)
    return out


def line_perm(g):
    """Induced permutation of lines."""
    idx = {L: w for w, L in enumerate(LSET)}
    return tuple(idx[frozenset(g[p] for p in L)] for L in LSET)


def orbits_of_line_sets(G, k):
    LP = [line_perm(g) for g in G]
    seen = set()
    reps = []
    for K in itertools.combinations(range(NPTS), k):
        K = frozenset(K)
        if K in seen:
            continue
        orb = {frozenset(lp[w] for w in K) for lp in LP}
        seen |= orb
        reps.append((tuple(sorted(K)), len(orb)))
    return reps



# ---------------------------------------------------------------- K-local cases
def or_table(T, n=13):
    m = 0
    for t in range(1 << n):
        if any((t >> i) & 1 for i in T):
            m |= 1 << t
    return m


def library(K):
    """ORs of 2, 3 and 4 points of every line outside K (a superset of the wires that any
    choice of private OR-tree shapes for those lines provides)."""
    lib, names = [], []
    for w in range(13):
        if w in K:
            continue
        for r in (2, 3, 4):
            for T in itertools.combinations(LINES[w], r):
                lib.append(or_table(T))
                names.append(T)
    return lib, names


def run_kloc(ks, deficit=False, plus=0, log=print, Kfilter=None):
    """For every orbit representative K of k-sets of lines: lines outside K are private 3-gate OR
    trees (cost 3(13-k)); the other 3k - 1 + plus gates (at most one NOT) must compute the lines of
    K, reading inputs and the library. plus = 1 gives 3k gates (must be SAT: validation)."""
    G = collineations()
    out = []
    for k in ks:
        for K, size in orbits_of_line_sets(G, k):
            if Kfilter and K not in Kfilter:
                continue
            lib, names = library(K)
            tabs = [ALL13[w] for w in K]
            Kl = [LINES[w] for w in K]
            s = 3 * k - 1 + plus
            ex = deficit_constraints(Kl, flag=None, min_total=2) if deficit else None
            if deficit in ('fam', 'famp'):
                ex = family_constraints(Kl, flag=None, min_total=2, famlines=LINES, perline=(deficit == 'famp'))
            t0 = time.time()
            log('K=%s (orbit size %d) free gates %d, library %d wires, deficit constraints %s' %
                (K, size, s, len(lib), deficit))
            r = cegis(13, tabs, Kl, s, maxnot=1, lib=lib, extra=ex, log=log)
            dt = time.time() - t0
            log('RESULT k=%d K=%s s=%d deficit=%s -> %s (%d iterations, %d rows, %.1fs)' %
                (k, K, s, deficit, r[0], r[3], len(r[2].rows), dt))
            if r[1]:
                log('  circuit %s' % (r[1],))
            out.append((k, K, s, r[0], dt))
    return out


# ---------------------------------------------------------------- C0 / C1 evaluation
def c01(gates, c):
    """The list with every NOT gate replaced by the constant c (AND [] = true, OR [] = false)."""
    return [(('and', []) if c else ('or', [])) if op == 'not' else (op, ins) for op, ins in gates]


def deficit_flags(n, lines, gates, outs):
    W1 = bit_wires(n, c01(gates, 1))
    W0 = bit_wires(n, c01(gates, 0))
    full = (1 << n) - 1
    res = []
    for w, L in enumerate(lines):
        m = full & ~sum(1 << i for i in L)
        if (W1[outs[w]] >> m) & 1:
            for u in L:
                if not ((W0[outs[w]] >> (1 << u)) & 1):
                    res.append((w, u))
    return res


# ---------------------------------------------------------------- validation
ONENOT5 = {0xfeeafcc0: 6, 0xeeeaeaea: 4, 0xeeeaeee8: 6, 0xeeeeeee0: 4, 0xfee8eee8: 8,
           0xfeeaeaaa: 8, 0xfeeaeae8: 9, 0xfeeaece8: 8, 0xfeeaeee0: 7, 0xfeeafcc8: 7}
FANO = [sorted({(u + w) % 7 for u in (0, 1, 3)}) for w in range(7)]


def _run(n, tabs, s, maxnot, lines=(), rows=None, **kw):
    rows = set(range(1 << n)) if rows is None else rows
    return cegis(n, tabs, lines, s, maxnot=maxnot, init_rows=rows, log=lambda m: None, **kw)


def validate(sections, log=print):
    ok = True
    t00 = time.time()
    if 'eval' in sections:
        g, o = plain_circuit()
        good = not check_all(13, ALL13, g, o, 0)
        rng = random.Random(5)
        W = bit_wires(13, g)
        for _ in range(300):
            t = rng.randrange(1 << 13)
            lw = lean_wires(g, [bool((t >> i) & 1) for i in range(13)])
            good &= all(lw[k] == bool((W[k] >> t) & 1) for k in range(len(lw)))
        log('eval: plain 39-gate list correct, bit-parallel = Lean-style evaluation: %s' % good)
        ok &= good
    if 'small' in sections:
        for name, n, T, b in (('xor2', 2, 0b0110, 4), ('xor3', 3, 0x96, 9), ('maj3', 3, 0xe8, 4)):
            lo, hi = _run(n, [T], b - 1, 1)[0], _run(n, [T], b, 1)[0]
            good = (lo == 'UNSAT' and hi == 'SAT')
            ok &= good
            log('%s one-NOT min %d: s=%d %s, s=%d %s %s' % (name, b, b - 1, lo, b, hi, 'ok' if good else 'MISMATCH'))
        for T, b in ONENOT5.items():
            lo, hi = _run(5, [T], b - 1, 1)[0], _run(5, [T], b, 1)[0]
            good = (lo == 'UNSAT' and hi == 'SAT')
            ok &= good
            log('5-input %#x one-NOT min %d (L-meta-1444): s=%d %s, s=%d %s %s' % (T, b, b - 1, lo, b, hi, 'ok' if good else 'MISMATCH'))
    if 'fano' in sections:
        tabs = line_tables(7, FANO)
        r14, r13 = _run(7, tabs, 14, 0, FANO)[0], _run(7, tabs, 13, 0, FANO)[0]
        good = (r14 == 'SAT' and r13 == 'UNSAT')
        ok &= good
        log('Fano monotone: s=14 %s, s=13 %s %s' % (r14, r13, 'ok' if good else 'MISMATCH'))
        # virtual rows / family bound: exactly one NOT at s = 14 must show >= 1 deficit flag
        for flag in (None, (0, 0)):
            ex = deficit_constraints(FANO, flag=flag, min_total=1, n=7) if flag else None
            r = _run(7, tabs, 14, 1, FANO, exact_not=1, extra=ex, sb_order=False, sb_distinct=False)
            msg = 'Fano exactly one NOT, s=14, deficit flag %s: %s' % (flag, r[0])
            if r[1]:
                d = deficit_flags(7, FANO, *r[1])
                msg += ', recomputed deficit flags %s' % (d,)
                good = (len(d) >= 1) and (flag is None or flag in d)
                ok &= good
            else:
                ok = False
            log(msg)
    if 'famfano' in sections:
        tabs = line_tables(7, FANO)
        for seed in (1, 2, 3):
            ex = family_constraints(FANO, flag=(0, 0), min_total=1, n=7)
            r = _run(7, tabs, 14, 1, FANO, exact_not=1, extra=ex, sb_order=False, sb_distinct=False, seed=seed)
            msg = 'Fano exactly one NOT, s=14, family bound + deficit flag (0,0), seed %d: %s' % (seed, r[0])
            if r[1]:
                d = deficit_flags(7, FANO, *r[1])
                msg += ', recomputed deficit flags %s' % (d,)
                ok &= (0, 0) in d
            else:
                ok = False
            log(msg)
        ex = family_constraints(FANO, flag=None, min_total=0, n=7)
        r = _run(7, tabs, 13, 1, FANO, extra=ex)
        log('Fano one-NOT s=13 with family bound: %s' % r[0])
    if 'famrandom' in sections:
        # random families of sets pairwise meeting in <= 1 point: minimum size of exactly-one-NOT
        # lists with and without the family bound must agree (the bound is a theorem)
        rng = random.Random(957)
        cnt = 0
        while cnt < int(os.environ.get('FAMRANDOM', '12')):
            n = rng.choice((5, 6))
            sets = []
            for _ in range(60):
                S = sorted(rng.sample(range(n), rng.choice((2, 3))))
                if all(len(set(S) & set(T)) <= 1 for T in sets) and S not in sets:
                    sets.append(S)
                if len(sets) == rng.choice((3, 4, 5)):
                    break
            if len(sets) < 2:
                continue
            cnt += 1
            tabs = line_tables(n, sets)
            plain = sum(len(S) - 1 for S in sets)
            res = {}
            for fb in (False, True):
                first = None
                for s in range(max(1, plain - 3), plain + 2):
                    ex = family_constraints(sets, flag=None, min_total=0, n=n) if fb else None
                    r = _run(n, tabs, s, 1, sets, exact_not=1, extra=ex)
                    if r[0] == 'SAT':
                        first = s
                        break
                res[fb] = first
            good = res[False] == res[True]
            ok &= good
            log('famrandom n=%d sets=%s plain=%d: first SAT size (exactly one NOT) without/with bound %s/%s %s' %
                (n, sets, plain, res[False], res[True], 'ok' if good else 'MISMATCH'))
    if 'famdef' in sections:
        # the family bound must not cut any list: smallest s with (exactly one NOT, deficit flag
        # (0, u) forced) must be the same with and without the bound
        fams = [(5, [[0, 1, 2], [2, 3, 4]]), (6, [[0, 1, 2], [2, 3, 4], [4, 5, 0]]),
                (6, [[0, 1, 2], [0, 3], [1, 4], [2, 5]]), (6, [[0, 1, 2, 3], [3, 4, 5]])]
        for n, sets in fams:
            tabs = line_tables(n, sets)
            plain = sum(len(S) - 1 for S in sets)
            for u in sets[0][:2]:
                res = {}
                for fb in (False, True):
                    first = None
                    for s in range(plain, plain + 8):
                        if fb:
                            ex = family_constraints(sets, flag=(0, u), min_total=1, n=n, perline=True)
                        else:
                            ex = deficit_constraints(sets, flag=(0, u), min_total=1, n=n)
                        r = _run(n, tabs, s, 1, sets, exact_not=1, extra=ex)
                        if r[0] == 'SAT':
                            d = deficit_flags(n, sets, *r[1])
                            assert (0, u) in d, 'virtual rows wrong'
                            first = s
                            break
                    res[fb] = first
                good = res[False] == res[True] and res[False] is not None
                ok &= good
                log('famdef n=%d sets=%s flag (0,%d): least s with a realized deficit, without/with bound: %s/%s %s' %
                    (n, sets, u, res[False], res[True], 'ok' if good else 'MISMATCH'))
    if 'mono39' in sections:
        rows = {0} | {1 << i for i in range(13)} | {8191 & ~sum(1 << i for i in L) for L in LINES}
        t0 = time.time()
        r = cegis(13, ALL13, LINES, 39, maxnot=0, init_rows=rows, sb_order=False, sb_distinct=False,
                  log=lambda m: None)
        log('q=3 monotone, s=39 (no symmetry breaking, minterm rows): %s %.1fs' % (r[0], time.time() - t0))
        ok &= r[0] == 'SAT'
    if 'klocsat' in sections:
        res = run_kloc([2, 3], plus=1, log=lambda m: None)
        good = all(x[3] == 'SAT' for x in res)
        ok &= good
        log('K-local with 3k gates (plain trees possible) SAT for k = 2, 3: %s %s' % ([x[3] for x in res], 'ok' if good else 'MISMATCH'))
    log('VALIDATION %s: all ok = %s (%.1fs)' % (','.join(sections), ok, time.time() - t00))
    return ok


ALL13 = line_tables()

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd', choices=['validate', 'kloc', 'full', 'group'])
    ap.add_argument('--sections', default='eval,small,fano,klocsat')
    ap.add_argument('--k', default='2,3,4')
    ap.add_argument('--K', default=None, help='only these orbit representatives, e.g. 0-1-2-3;0-1-2-4')
    ap.add_argument('--deficit', action='store_true')
    ap.add_argument('--kfam', action='store_true', help='kloc: family bound constraints')
    ap.add_argument('--s', type=int, default=38)
    ap.add_argument('--flag', default='0,0')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--nosb', action='store_true')
    ap.add_argument('--fambound', action='store_true')
    ap.add_argument('--perline', action='store_true')
    a = ap.parse_args()
    lg = lambda m: print(m, flush=True)
    if a.cmd == 'group':
        G = collineations()
        lg('collineation group order %d' % len(G))
        for k in range(1, 8):
            lg('k=%d orbits %s' % (k, orbits_of_line_sets(G, k)))
    elif a.cmd == 'validate':
        validate(a.sections.split(','), lg)
    elif a.cmd == 'kloc':
        Kf = None
        if a.K:
            Kf = [tuple(int(x) for x in K.split('-')) for K in a.K.split(';')]
        run_kloc([int(x) for x in a.k.split(',')], deficit=(('famp' if a.perline else 'fam') if a.kfam else a.deficit), log=lg, Kfilter=Kf)
    elif a.cmd == 'full':
        flag = tuple(int(x) for x in a.flag.split(',')) if a.flag != 'none' else None
        ex = deficit_constraints(LINES, flag=flag, min_total=2) if a.deficit else None
        if a.fambound:
            ex = family_constraints(LINES, flag=flag, min_total=2, perline=a.perline)
        r = cegis(13, ALL13, LINES, a.s, maxnot=1, extra=ex, log=lg, seed=a.seed,
                  sb_order=not a.nosb, sb_distinct=not a.nosb)
        lg('RESULT full s=%d deficit=%s fambound=%s flag=%s -> %s (%d rows)' % (a.s, a.deficit, a.fambound, flag, r[0], len(r[2].rows)))
        if r[1]:
            lg('  circuit %s' % (r[1],))
