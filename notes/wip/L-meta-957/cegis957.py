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


if __name__ == '__main__':
    pass


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
