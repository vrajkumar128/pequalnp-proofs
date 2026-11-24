#!/usr/bin/env python3
"""Exact-synthesis SAT search for monotone fan-in-2 AND/OR circuits computing a graph's
edge function f_G(x) = OR_{uv in E} (x_u AND x_v), optionally with a "dirty" row D:
some AND gate must evaluate to true on the input whose true set is exactly D.

Normal form searched (class N_s): exactly s gates; gate j is wire n+j; every gate reads
exactly two DISTINCT earlier wires a<b; op AND/OR; output = last gate; every gate other
than the last is read by a later gate (live); gates are in greedy-canonical order
(for p<q: if both inputs of q are wires < n+p then key(p) < key(q), key = (colex pair
index, op) with OR<AND); this also excludes structural duplicates.

Rows: the edges of G (output 1), the maximal independent sets of G (output 0), plus D.
For a monotone circuit these rows determine the computed function (see report).

Usage:
  shard_search.py validate               small cases with known answers (pysat CaDiCaL 1.9.5)
  shard_search.py dimacs OUT.cnf S [flags]        main instance (shard D={0,2,3,4}, size S)
      flags: --encB (encoding B) --rs=P1,P2,MIS (restriction lower-bound constraints)
             --lcache=FILE (cache of least sizes of small subgraphs) --noorder --inj --extra --mono
  shard_search.py decode SOLVER_OUT OUT.cnf S [flags]   decode a model, verify on all 2^n inputs
"""
import itertools, json, os, sys, time

MAIN_N = 11
MAIN_EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8),
              (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
MAIN_DIRTY = (0, 2, 3, 4)
MAIN_S = 21
OPTS = {}


def edge_fn(edges, x):
    return any(x[u] and x[v] for (u, v) in edges)


def maximal_independent_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    res = []
    for mask in range(1 << n):
        inside = [(mask >> i) & 1 for i in range(n)]
        if any(inside[u] and inside[v] for (u, v) in edges):
            continue
        if all(inside[i] or any(inside[v] for v in adj[i]) for i in range(n)):
            res.append(tuple(i for i in range(n) if inside[i]))
    return res


def rows_for(n, edges, dirty, extra_sets=()):
    rows = []
    for (u, v) in edges:
        rows.append(((u, v), True))
    for m in maximal_independent_sets(n, edges):
        rows.append((m, False))
    if OPTS.get('extra'):
        es = set(tuple(sorted(e)) for e in edges)
        for u in range(n):
            rows.append(((u,), False))
        for u in range(n):
            for v in range(u + 1, n):
                if (u, v) not in es:
                    rows.append(((u, v), False))
    have = set(frozenset(st) for (st, _) in rows)
    for st in extra_sets:
        if frozenset(st) not in have:
            have.add(frozenset(st))
            rows.append((tuple(st), edge_fn(edges, [i in st for i in range(n)])))
    dirty_row = None
    if dirty is not None:
        d = tuple(sorted(dirty))
        for k, (st, _) in enumerate(rows):
            if tuple(sorted(st)) == d:
                dirty_row = k
        if dirty_row is None:
            x = [i in d for i in range(n)]
            rows.append((d, edge_fn(edges, x)))
            dirty_row = len(rows) - 1
    return rows, dirty_row


class CNF:
    def __init__(self):
        self.nv = 1          # var 1 is the constant TRUE
        self.clauses = [[1]]

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        out = []
        for l in cl:
            if l == 1:
                return
            if l == -1:
                continue
            if -l in out:
                return
            if l not in out:
                out.append(l)
        self.clauses.append(out)


def npairs(m):
    return m * (m - 1) // 2


def add_monotonicity(cnf, rows, s, g):
    """Each gate computes a monotone function: value on row t implies value on every row t' ⊇ t."""
    sets = [frozenset(st) for (st, _) in rows]
    for t in range(len(rows)):
        for t2 in range(len(rows)):
            if t != t2 and sets[t] < sets[t2]:
                for j in range(s):
                    cnf.add([-g[j][t], g[j][t2]])


def add_row_injectivity(cnf, n, s, R, rowx, g):
    """Every gate's vector of values on the rows differs from that of every earlier wire."""
    for j in range(s):
        for w in range(n):
            cnf.add([(-g[j][t] if rowx[t][w] else g[j][t]) for t in range(R)])
        for k in range(j):
            es = []
            for t in range(R):
                e = cnf.new()
                cnf.add([-e, g[k][t], g[j][t]])
                cnf.add([-e, -g[k][t], -g[j][t]])
                es.append(e)
            cnf.add(es)


def atmost_seq(cnf, xs, k):
    """Sinz sequential counter: at most k of the literals xs are true."""
    m = len(xs)
    if k >= m:
        return
    if k <= 0:
        for x in xs:
            cnf.add([-x])
        return
    r = [[cnf.new() for _ in range(k)] for _ in range(m)]
    for i in range(m):
        x = xs[i]
        cnf.add([-x, r[i][0]])
        if i > 0:
            for c in range(k):
                cnf.add([-r[i - 1][c], r[i][c]])
            for c in range(1, k):
                cnf.add([-x, -r[i - 1][c - 1], r[i][c]])
            cnf.add([-x, -r[i - 1][k - 1]])


def add_zero_restrictions(cnf, n, s, op, A, B, restr):
    """Gate elimination by the restriction x_v = 0 (v in S). A wire is Z (constant 0 under the
    restriction) if it is x_v with v in S, an AND gate with a Z input, or an OR gate with two
    Z inputs. A gate with a Z input is eliminated (it is Z, or an OR gate that copies its other
    input). The remaining gates, with copies redirected, form a Monotone2 circuit computing
    f restricted, i.e. f_{G-S}; so at most s - L(G-S) gates are eliminated, where L(H) is the
    least size of a Monotone2 circuit for f_H (computed by least_size below)."""
    T = 1
    for (Sset, bound) in restr:
        Z = [(T if w in Sset else -T) for w in range(n)]
        elims = []
        for j in range(s):
            za, zb = cnf.new(), cnf.new()
            for w in range(n + j):
                cnf.add([-A[j][w], -Z[w], za])
                cnf.add([-A[j][w], Z[w], -za])
                cnf.add([-B[j][w], -Z[w], zb])
                cnf.add([-B[j][w], Z[w], -zb])
            o = op[j]
            zj = cnf.new()
            cnf.add([-o, -za, zj])
            cnf.add([-o, -zb, zj])
            cnf.add([o, -za, -zb, zj])
            cnf.add([-zj, za, zb])
            cnf.add([o, -zj, za])
            cnf.add([o, -zj, zb])
            Z.append(zj)
            e = cnf.new()
            cnf.add([-za, e])
            cnf.add([-zb, e])
            cnf.add([-e, za, zb])
            elims.append(e)
        atmost_seq(cnf, elims, bound)


_LCACHE = {}


def canon_graph(edges):
    vs = sorted(set(v for e in edges for v in e))
    k = len(vs)
    idx = {v: i for i, v in enumerate(vs)}
    es = [(idx[u], idx[v]) for (u, v) in edges]
    best = None
    for p in itertools.permutations(range(k)):
        c = tuple(sorted(tuple(sorted((p[u], p[v]))) for (u, v) in es))
        if best is None or c < best:
            best = c
    return k, best


def least_size(edges):
    """Proven lower bound on the least size of a Monotone2 circuit for f_H (H = the given
    edges, isolated vertices dropped): every size below it is UNSAT. Without a time budget
    (OPTS['budget']) it is exact (SAT at that size, circuit decoded and verified)."""
    if not edges:
        return 0
    k, c = canon_graph(edges)
    if (k, c) in _LCACHE:
        return _LCACHE[(k, c)]
    key = repr((k, c))
    if OPTS.get('lcache') and os.path.exists(OPTS['lcache']):
        with open(OPTS['lcache']) as f:
            disk = json.load(f)
        if key in disk:
            _LCACHE[(k, c)] = disk[key]
            return disk[key]
    saved = dict(OPTS)
    OPTS.clear()
    for key_ in ('rs', 'lcache', 'budget'):
        if key_ in saved:
            OPTS[key_] = saved[key_]
    # proven lower bound: sizes 1..lb-1 are UNSAT; lb is exact when SAT was reached at lb
    lb = 1
    for size in range(1, 41):
        cnf, meta = encode_b(k, list(c), size, None)
        r, m = solve_pysat(cnf, budget=OPTS.get('budget'))
        if r is True:
            gates = decode(meta, m)
            assert verify(k, list(c), gates, k + size - 1)[0]
            lb = size
            break
        if r is None:
            lb = size
            break
        lb = size + 1
    OPTS.clear()
    OPTS.update(saved)
    s = lb
    _LCACHE[(k, c)] = s
    if OPTS.get('lcache'):
        disk = {}
        if os.path.exists(OPTS['lcache']):
            with open(OPTS['lcache']) as f:
                disk = json.load(f)
        disk[key] = s
        with open(OPTS['lcache'], 'w') as f:
            json.dump(disk, f)
    return s


def zero_restrictions_for(n, edges, s, sizes):
    out = []
    for m in sizes:
        for Sset in itertools.combinations(range(n), m):
            sub = [(u, v) for (u, v) in edges if u not in Sset and v not in Sset]
            L = least_size(sub)
            out.append((set(Sset), s - L, L))
    return out


def restricted_least_size(n, edges, P, Q):
    """Lower bound (in fact the exact value) for the least Monotone2 size of f restricted by
    x_P = 1, x_Q = 0 (P independent). The restricted function is OR_{a in A} x_a OR f_H with
    A = N(P) minus Q, H = G minus (P, Q, N(P)). L(OR_A x OR f_H) >= |A| + L(H) if H has an edge
    (each x_a is read by some gate, and x_a = 0 eliminates it; induct on |A|), >= |A| - 1 if
    H has no edge, and L(H) is computed by least_size."""
    P, Q = set(P), set(Q)
    nb = set()
    for (u, v) in edges:
        if u in P:
            nb.add(v)
        if v in P:
            nb.add(u)
    A = nb - Q - P
    gone = P | Q | nb
    H = [(u, v) for (u, v) in edges if u not in gone and v not in gone]
    if H:
        return len(A) + least_size(H)
    return max(len(A) - 1, 0)


def restriction_family(n, edges, fam):
    """fam: set of tags. 'P1': x_v = 1; 'P2': x_u = x_v = 1 (u, v non-adjacent);
    'P1Q1': x_v = 1, x_w = 0; 'MIS': x_M = 1 for each maximal independent set M."""
    es = set(tuple(sorted(e)) for e in edges)
    verts = sorted(set(v for e in edges for v in e))
    out = []
    if 'P1' in fam:
        for v in verts:
            out.append(((v,), ()))
    if 'P2' in fam:
        for u, v in itertools.combinations(verts, 2):
            if (u, v) not in es:
                out.append(((u, v), ()))
    if 'P1Q1' in fam:
        for v in verts:
            for w in verts:
                if w != v:
                    out.append(((v,), (w,)))
    if 'MIS' in fam:
        for m in maximal_independent_sets(n, edges):
            out.append((tuple(m), ()))
    return out


def add_restrictions(cnf, n, s, rows, va, vb, restr):
    """restr: list of (P, Q, L). Under the restriction x_P = 1, x_Q = 0 a wire w is constant iff
    w(P) = 1 (constant 1; row P has exactly P true) or w(V minus Q) = 0 (constant 0). A gate
    with a constant input is constant or a copy of its other input, so it is eliminated; the
    other gates form a Monotone2 circuit for f restricted. So at most s - L gates have a
    constant input."""
    idx = {}
    for t, (st, _) in enumerate(rows):
        idx[frozenset(st)] = t
    for (P, Q, L) in restr:
        bound = s - L
        t0 = idx[frozenset(P)] if P else None
        t1 = idx[frozenset(set(range(n)) - set(Q))] if Q else None
        es = []
        for j in range(s):
            e = cnf.new()
            for v in (va[j], vb[j]):
                if t0 is not None:
                    cnf.add([-v[t0], e])
                if t1 is not None:
                    cnf.add([v[t1], e])
            es.append(e)
        atmost_seq(cnf, es, bound)


def restriction_rows(n, edges, restr):
    sets = []
    for (P, Q, L) in restr:
        if P:
            sets.append(tuple(sorted(P)))
        if Q:
            sets.append(tuple(sorted(set(range(n)) - set(Q))))
    return sets


def encode(n, edges, s, dirty=None, order=True, live=True, inputs_used=True, inj=False):
    T, F = 1, -1
    rows, drow = rows_for(n, edges, dirty)
    R = len(rows)
    rowx = [[(i in st) for i in range(n)] for (st, _) in rows]
    cnf = CNF()
    W = n + s
    pairs = [(a, b) for b in range(W) for a in range(b)]   # colex: idx = b(b-1)/2 + a
    op = [cnf.new() for _ in range(s)]                       # true = AND
    S = [[cnf.new() for _ in range(npairs(n + j))] for j in range(s)]
    U = [[None] + [cnf.new() for _ in range(1, npairs(n + j))] for j in range(s)]

    def Ul(j, i):
        if i <= 0:
            return T
        if i >= npairs(n + j):
            return F
        return U[j][i]

    for j in range(s):
        Pj = npairs(n + j)
        for i in range(Pj):
            cnf.add([-Ul(j, i), Ul(j, i + 1), S[j][i]])
            cnf.add([-S[j][i], Ul(j, i)])
            cnf.add([-S[j][i], -Ul(j, i + 1)])
            if i >= 1:
                cnf.add([-Ul(j, i + 1), Ul(j, i)])
    g = [[cnf.new() for _ in range(R)] for j in range(s)]

    def val(w, t):
        if w < n:
            return T if rowx[t][w] else F
        return g[w - n][t]

    for j in range(s):
        o = op[j]
        for i in range(npairs(n + j)):
            a, b = pairs[i]
            sv = S[j][i]
            for t in range(R):
                xa, xb, G = val(a, t), val(b, t), g[j][t]
                cnf.add([-sv, xa, xb, -G])
                cnf.add([-sv, -xa, -xb, G])
                cnf.add([-sv, -o, xa, -G])
                cnf.add([-sv, -o, xb, -G])
                cnf.add([-sv, o, -xa, G])
                cnf.add([-sv, o, -xb, G])
    for t in range(R):
        cnf.add([g[s - 1][t] if rows[t][1] else -g[s - 1][t]])
    if drow is not None:
        ds = []
        for j in range(s):
            d = cnf.new()
            cnf.add([-d, op[j]])
            cnf.add([-d, g[j][drow]])
            ds.append(d)
        cnf.add(ds)
    if live:
        for j in range(s - 1):
            w = n + j
            cl = []
            for k in range(j + 1, s):
                for i in range(npairs(n + k)):
                    if w in pairs[i]:
                        cl.append(S[k][i])
            cnf.add(cl)
    if inputs_used:
        for w in sorted(set(v for e in edges for v in e)):
            cl = []
            for k in range(s):
                for i in range(npairs(n + k)):
                    if w in pairs[i]:
                        cl.append(S[k][i])
            cnf.add(cl)
    if order:
        for p in range(s):
            for q in range(p + 1, s):
                for i in range(npairs(n + p)):
                    cnf.add([-S[q][i], -Ul(p, i + 1)])
                    cnf.add([-S[q][i], -S[p][i], -op[p]])
                    cnf.add([-S[q][i], -S[p][i], op[q]])
    if inj:
        add_row_injectivity(cnf, n, s, R, rowx, g)
    if OPTS.get('mono'):
        add_monotonicity(cnf, rows, s, g)
    meta = dict(n=n, s=s, op=op, S=S, pairs=pairs, rows=rows, drow=drow)
    return cnf, meta


def encode_b(n, edges, s, dirty=None, order=True, live=True, inputs_used=True, inj=False):
    """Encoding B: separate one-hot selectors for the smaller input a and the larger input b
    (order-encoded ladders), per-row selected-input values va, vb. Same class N_s and same
    greedy order (key = (b, a, op), lexicographic, OR < AND) as encode()."""
    T, F = 1, -1
    restr = []
    if OPTS.get('rs'):
        for (P_, Q_) in restriction_family(n, edges, OPTS['rs']):
            L_ = restricted_least_size(n, edges, P_, Q_)
            if L_ > 0:
                restr.append((P_, Q_, L_))
    rows, drow = rows_for(n, edges, dirty, restriction_rows(n, edges, restr))
    R = len(rows)
    rowx = [[(i in st) for i in range(n)] for (st, _) in rows]
    cnf = CNF()
    op = [cnf.new() for _ in range(s)]
    A = [[cnf.new() for _ in range(n + j)] for j in range(s)]
    B = [[cnf.new() for _ in range(n + j)] for j in range(s)]
    UA = [[None] + [cnf.new() for _ in range(1, n + j)] for j in range(s)]
    UB = [[None] + [cnf.new() for _ in range(1, n + j)] for j in range(s)]

    def lad(X, UX, j):
        m = n + j
        def ul(i):
            if i <= 0:
                return T
            if i >= m:
                return F
            return UX[j][i]
        for i in range(m):
            cnf.add([-ul(i), ul(i + 1), X[j][i]])
            cnf.add([-X[j][i], ul(i)])
            cnf.add([-X[j][i], -ul(i + 1)])
            if i >= 1:
                cnf.add([-ul(i + 1), ul(i)])
        return ul

    ulA = [None] * s
    ulB = [None] * s
    for j in range(s):
        ulA[j] = lad(A, UA, j)
        ulB[j] = lad(B, UB, j)
        for a in range(n + j):
            cnf.add([-A[j][a], ulB[j](a + 1)])          # a < b
    g = [[cnf.new() for _ in range(R)] for j in range(s)]
    va = [[cnf.new() for _ in range(R)] for j in range(s)]
    vb = [[cnf.new() for _ in range(R)] for j in range(s)]

    def val(w, t):
        if w < n:
            return T if rowx[t][w] else F
        return g[w - n][t]

    for j in range(s):
        o = op[j]
        for t in range(R):
            for w in range(n + j):
                x = val(w, t)
                cnf.add([-A[j][w], -x, va[j][t]])
                cnf.add([-A[j][w], x, -va[j][t]])
                cnf.add([-B[j][w], -x, vb[j][t]])
                cnf.add([-B[j][w], x, -vb[j][t]])
            G, xa, xb = g[j][t], va[j][t], vb[j][t]
            cnf.add([xa, xb, -G])
            cnf.add([-xa, -xb, G])
            cnf.add([-o, xa, -G])
            cnf.add([-o, xb, -G])
            cnf.add([o, -xa, G])
            cnf.add([o, -xb, G])
    for t in range(R):
        cnf.add([g[s - 1][t] if rows[t][1] else -g[s - 1][t]])
    if drow is not None:
        ds = []
        for j in range(s):
            d = cnf.new()
            cnf.add([-d, op[j]])
            cnf.add([-d, g[j][drow]])
            ds.append(d)
        cnf.add(ds)
    if live:
        for j in range(s - 1):
            w = n + j
            cnf.add([X[k][w] for k in range(j + 1, s) for X in (A, B)])
    if inputs_used:
        for w in sorted(set(v for e in edges for v in e)):
            cnf.add([X[k][w] for k in range(s) for X in (A, B)])
    if order:
        for p in range(s):
            for q in range(p + 1, s):
                eqb = cnf.new()
                eqab = cnf.new()
                for beta in range(n + p):
                    cnf.add([-B[q][beta], -ulB[p](beta + 1)])
                    cnf.add([-B[q][beta], -B[p][beta], eqb])
                for alpha in range(n + q):
                    if alpha < n + p:
                        cnf.add([-eqb, -A[q][alpha], -ulA[p](alpha + 1)])
                        cnf.add([-eqb, -A[q][alpha], -A[p][alpha], eqab])
                cnf.add([-eqab, -op[p]])
                cnf.add([-eqab, op[q]])
    if inj:
        add_row_injectivity(cnf, n, s, R, rowx, g)
    if OPTS.get('mono'):
        add_monotonicity(cnf, rows, s, g)
    if restr:
        add_restrictions(cnf, n, s, rows, va, vb, restr)
    if OPTS.get('zr'):
        add_zero_restrictions(cnf, n, s, op, A, B, [(S_, b_) for (S_, b_, L_) in
                              zero_restrictions_for(n, edges, s, OPTS['zr'])])
    meta = dict(n=n, s=s, op=op, A=A, B=B, rows=rows, drow=drow, enc='B')
    return cnf, meta


def decode(meta, model_set):
    n, s = meta['n'], meta['s']
    gates = []
    if meta.get('enc') == 'B':
        for j in range(s):
            sa = [i for i, v in enumerate(meta['A'][j]) if v in model_set]
            sb = [i for i, v in enumerate(meta['B'][j]) if v in model_set]
            assert len(sa) == 1 and len(sb) == 1 and sa[0] < sb[0], (sa, sb)
            gates.append(('AND' if meta['op'][j] in model_set else 'OR', [sa[0], sb[0]]))
        return gates
    for j in range(s):
        sel = [i for i, v in enumerate(meta['S'][j]) if v in model_set]
        assert len(sel) == 1, sel
        a, b = meta['pairs'][sel[0]]
        gates.append(('AND' if meta['op'][j] in model_set else 'OR', [a, b]))
    return gates


def lean_eval(n, gates, output, x):
    """Mirror of Circuit.wires / Circuit.eval in Defs/CircuitLowerBounds.lean."""
    w = list(x)
    for (o, inp) in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        w.append(all(vals) if o == 'AND' else any(vals))
    return (w[output] if output < len(w) else False), w


def verify(n, edges, gates, output, dirty=None):
    ok = True
    for mask in range(1 << n):
        x = [bool((mask >> i) & 1) for i in range(n)]
        v, _ = lean_eval(n, gates, output, x)
        if v != edge_fn(edges, x):
            ok = False
            break
    dirty_ok = None
    if dirty is not None:
        x = [i in dirty for i in range(n)]
        _, w = lean_eval(n, gates, output, x)
        dirty_ok = any(gates[j][0] == 'AND' and w[n + j] for j in range(len(gates)))
    return ok, dirty_ok


def solve_pysat(cnf, name='cadical195', budget=None):
    """Returns (True, model) / (False, None) / (None, None) if the time budget ran out."""
    from pysat.solvers import Solver
    import threading
    with Solver(name=name, bootstrap_with=cnf.clauses) as sv:
        if budget is None:
            r = sv.solve()
            m = sv.get_model() if r else None
            return r, (set(l for l in m if l > 0) if m else None)
    # with a time budget: external kissat binary, killed after `budget` seconds
    import subprocess, tempfile
    here = os.path.dirname(os.path.abspath(__file__))
    kissat = os.path.join(here, 'src', 'kissat', 'build', 'kissat')
    fd, path = tempfile.mkstemp(suffix='.cnf', dir=os.path.join(here, 'runs'))
    os.close(fd)
    write_dimacs(cnf, path)
    try:
        pr = subprocess.run(['timeout', str(int(budget)), kissat, '-q', path],
                            capture_output=True, text=True)
    finally:
        os.remove(path)
    out = pr.stdout.splitlines()
    if any(l.startswith('s UNSATISFIABLE') for l in out):
        return False, None
    if any(l.startswith('s SATISFIABLE') for l in out):
        lits = []
        for l in out:
            if l.startswith('v '):
                lits += [int(z) for z in l.split()[1:]]
        return True, set(l for l in lits if l > 0)
    return None, None


def min_size(n, edges, dirty=None, smax=12, **kw):
    """Smallest s <= smax with a circuit in N_s (SAT), checking UNSAT below."""
    res = {}
    for s in range(1, smax + 1):
        enc = kw.pop('enc', 'A') if 'enc' in kw else 'A'
        cnf, meta = (encode_b if enc == 'B' else encode)(n, edges, s, dirty, **kw)
        kw['enc'] = enc
        r, m = solve_pysat(cnf)
        res[s] = r
        if r:
            gates = decode(meta, m)
            ok, dok = verify(n, edges, gates, n + s - 1, dirty)
            assert ok, ('decoded circuit wrong', gates)
            if dirty is not None:
                assert dok, ('decoded circuit not dirty', gates)
            return s, gates, res
    return None, None, res


def brute_exists(n, edges, s, dirty):
    """Independent exhaustive search (no SAT, no ordering, no dedup): exactly s gates, each
    AND/OR of two distinct earlier wires, every gate but the last read later, output = last
    gate, computes f_G on all 2^n inputs, and (if dirty) some AND gate is true at row D."""
    N = 1 << n
    tts = [sum(1 << m for m in range(N) if (m >> i) & 1) for i in range(n)]
    f = sum(1 << m for m in range(N)
            if edge_fn(edges, [bool((m >> i) & 1) for i in range(n)]))
    dbit = None if dirty is None else sum(1 << i for i in dirty)
    ops = []
    used = [0] * (n + s)

    def rec(j):
        if j == s:
            return (tts[-1] == f and all(used[n + k] for k in range(s - 1)) and
                    (dbit is None or any(ops[k] == 'AND' and (tts[n + k] >> dbit) & 1
                                         for k in range(s))))
        unused = sum(1 for k in range(j) if used[n + k] == 0)
        r = s - j
        for b in range(n + j):
            for a in range(b):
                nu = unused + 1 - (a >= n and used[a] == 0) - (b >= n and used[b] == 0)
                if nu - (r - 1) > 1:
                    continue
                for o in ('AND', 'OR'):
                    tts.append((tts[a] & tts[b]) if o == 'AND' else (tts[a] | tts[b]))
                    ops.append(o)
                    used[a] += 1
                    used[b] += 1
                    if rec(j + 1):
                        return True
                    tts.pop()
                    ops.pop()
                    used[a] -= 1
                    used[b] -= 1
        return False
    return rec(0)


def graphs_upto_iso(n):
    allpairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    seen, out = set(), []
    for k in range(1, len(allpairs) + 1):
        for es in itertools.combinations(allpairs, k):
            c = min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in es))
                    for p in itertools.permutations(range(n)))
            if c not in seen:
                seen.add(c)
                out.append(list(es))
    return out


def validate():
    t0 = time.time()
    saved = dict(OPTS)
    OPTS.clear()
    cases = [
        ('P4', 4, [(0, 1), (1, 2), (2, 3)], 4),
        ('K13', 4, [(0, 1), (0, 2), (0, 3)], 3),
        ('C5', 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 7),
        ('P5', 5, [(0, 1), (1, 2), (2, 3), (3, 4)], 5),
        ('C4', 4, [(0, 1), (1, 2), (2, 3), (3, 0)], 3),
        ('K3', 3, [(0, 1), (1, 2), (0, 2)], 4),
        ('C6', 6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)], 8),
    ]
    allok = True
    configs = [('A', True, None), ('A', False, None), ('B', True, None), ('B', False, None),
               ('B', True, {'P1', 'P2', 'P1Q1', 'MIS'})]
    # 1. known exact sizes: SAT at the known size, UNSAT at every smaller size
    for name, n, edges, known in cases:
        for enc, order, rs in configs:
            OPTS.clear()
            if rs:
                OPTS['rs'] = rs
            s, gates, res = min_size(n, edges, None, smax=known + 1, order=order, enc=enc)
            ok = (s == known) and all(res[k] is False for k in range(1, known))
            allok &= ok
            print(f'{name}: enc={enc} order={order} rs={sorted(rs) if rs else None} min size {s}'
                  f' (known {known}) {"OK" if ok else "MISMATCH"}', flush=True)
    # 2. every graph on 4 vertices (up to isomorphism), without and with each dirty row
    #    (each maximal independent set): least size <= 5 by exhaustive search vs. SAT
    checked = mism = 0
    for edges in graphs_upto_iso(4):
        for D in [None] + maximal_independent_sets(4, edges):
            sb = next((s for s in range(1, 6) if brute_exists(4, edges, s, D)), None)
            got = []
            for enc, order, rs in configs:
                OPTS.clear()
                if rs:
                    OPTS['rs'] = rs
                got.append(min_size(4, edges, D, smax=5, order=order, enc=enc)[0])
            checked += 1
            if any(g != sb for g in got):
                mism += 1
                allok = False
                print('MISMATCH', edges, D, sb, got, flush=True)
    print(f'4-vertex graphs x dirty rows: {checked} cases, {mism} mismatches', flush=True)
    OPTS.clear()
    OPTS.update(saved)
    print('validate time %.1fs, all ok: %s' % (time.time() - t0, allok))
    return allok


def write_dimacs(cnf, path):
    with open(path, 'w') as f:
        f.write('p cnf %d %d\n' % (cnf.nv, len(cnf.clauses)))
        for c in cnf.clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')


def build_main_from_argv(argv):
    """Instance for the main step: G (11 vertices, 16 edges), dirty row D = {0,2,3,4}.
    argv: OUT S [--encB] [--rs=TAGS] [--lcache=FILE] [--extra] [--mono] [--inj] [--noorder]"""
    for a in argv:
        if a.startswith('--rs='):
            OPTS['rs'] = set(a[5:].split(','))
        if a.startswith('--lcache='):
            OPTS['lcache'] = a[9:]
        if a.startswith('--budget='):
            OPTS['budget'] = float(a[9:])
    OPTS['extra'] = '--extra' in argv
    OPTS['mono'] = '--mono' in argv
    s = int(argv[1]) if len(argv) > 1 and not argv[1].startswith('--') else MAIN_S
    order = '--noorder' not in argv
    encf = encode_b if '--encB' in argv else encode
    cnf, meta = encf(MAIN_N, MAIN_EDGES, s, MAIN_DIRTY, order=order, inj='--inj' in argv)
    return s, cnf, meta


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    cmd = sys.argv[1]
    if cmd == 'validate':
        validate()
    elif cmd == 'dimacs':
        s, cnf, meta = build_main_from_argv(sys.argv[2:])
        write_dimacs(cnf, sys.argv[2])
        print('wrote %s: s=%d vars=%d clauses=%d rows=%d dirty_row=%s' %
              (sys.argv[2], s, cnf.nv, len(cnf.clauses), len(meta['rows']), meta['drow']))
    elif cmd == 'decode':
        # decode SOLVER_OUTPUT OUT.cnf S [same flags as dimacs]
        sol = sys.argv[2]
        s, cnf, meta = build_main_from_argv(sys.argv[3:])
        with open(sys.argv[3]) as f:
            hdr = f.readline().split()
        assert int(hdr[2]) == cnf.nv and int(hdr[3]) == len(cnf.clauses), 'CNF mismatch'
        lits = []
        with open(sol) as f:
            for line in f:
                if line.startswith('v '):
                    lits += [int(z) for z in line.split()[1:]]
        m = set(l for l in lits if l > 0)
        gates = decode(meta, m)
        ok, dok = verify(MAIN_N, MAIN_EDGES, gates, MAIN_N + s - 1, MAIN_DIRTY)
        print('gates:', gates)
        print('computes f on all 2048 inputs:', ok, ' dirty AND at D:', dok)
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
