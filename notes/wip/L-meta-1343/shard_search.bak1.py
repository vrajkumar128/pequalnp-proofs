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
  shard_search.py dimacs OUT.cnf [s] [--noorder]   main instance (shard D={0,2,3,4}, s=21)
  shard_search.py decode OUT.cnf SOLVER_OUTPUT     decode a model, verify on all 2^n inputs
"""
import itertools, sys, time

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


def rows_for(n, edges, dirty):
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
    """Least size of a Monotone2 circuit for f_H (H = the given edges, isolated vertices
    dropped): SAT at that size (circuit decoded and verified), UNSAT at every smaller size."""
    if not edges:
        return 0
    k, c = canon_graph(edges)
    if (k, c) in _LCACHE:
        return _LCACHE[(k, c)]
    saved = dict(OPTS)
    OPTS.clear()
    s, gates, res = min_size(k, list(c), None, smax=40, enc='B')
    OPTS.update(saved)
    assert s is not None and all(res[t] is False for t in range(1, s))
    _LCACHE[(k, c)] = s
    return s


def zero_restrictions_for(n, edges, s, sizes):
    out = []
    for m in sizes:
        for Sset in itertools.combinations(range(n), m):
            sub = [(u, v) for (u, v) in edges if u not in Sset and v not in Sset]
            L = least_size(sub)
            out.append((set(Sset), s - L, L))
    return out


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
    rows, drow = rows_for(n, edges, dirty)
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


def solve_pysat(cnf, name='cadical195'):
    from pysat.solvers import Solver
    with Solver(name=name, bootstrap_with=cnf.clauses) as sv:
        r = sv.solve()
        m = sv.get_model() if r else None
    return r, (set(l for l in m if l > 0) if m else None)


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


def validate():
    t0 = time.time()
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
    for name, n, edges, known in cases:
        for enc, order in (('A', True), ('A', False), ('B', True), ('B', False)):
            s, gates, res = min_size(n, edges, None, smax=known + 1, order=order, enc=enc)
            ok = (s == known) and all(res[k] is False for k in range(1, known))
            allok &= ok
            print(f'{name}: enc={enc} order={order} min size {s} (known {known}) '
                  f'{"OK" if ok else "MISMATCH"}  {gates}', flush=True)
    print('validate time %.1fs, all ok: %s' % (time.time() - t0, allok))
    return allok


def write_dimacs(cnf, path):
    with open(path, 'w') as f:
        f.write('p cnf %d %d\n' % (cnf.nv, len(cnf.clauses)))
        for c in cnf.clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return
    cmd = sys.argv[1]
    if cmd == 'validate':
        validate()
    elif cmd == 'dimacs':
        OPTS['extra'] = '--extra' in sys.argv
        OPTS['mono'] = '--mono' in sys.argv
        s = int(sys.argv[3]) if len(sys.argv) > 3 and not sys.argv[3].startswith('--') else MAIN_S
        order = '--noorder' not in sys.argv
        encf = encode_b if '--encB' in sys.argv else encode
        cnf, meta = encf(MAIN_N, MAIN_EDGES, s, MAIN_DIRTY, order=order, inj='--inj' in sys.argv)
        write_dimacs(cnf, sys.argv[2])
        print('wrote %s: s=%d vars=%d clauses=%d rows=%d dirty_row=%s' %
              (sys.argv[2], s, cnf.nv, len(cnf.clauses), len(meta['rows']), meta['drow']))
    elif cmd == 'decode':
        s = MAIN_S
        with open(sys.argv[2]) as f:
            hdr = f.readline().split()
        cnf, meta = encode(MAIN_N, MAIN_EDGES, s, MAIN_DIRTY)
        assert int(hdr[2]) == cnf.nv, 'header mismatch (different s?)'
        lits = []
        with open(sys.argv[3]) as f:
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
