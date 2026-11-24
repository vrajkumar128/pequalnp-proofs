#!/usr/bin/env python3
"""L-meta-1342, junk-AND shards: exact-synthesis SAT encoder + driver + validation.

Class K(s, k) searched (NF = normal form):
  exactly s gates; gate j is wire n+j; each gate is AND or OR of two DISTINCT earlier wires a<b;
  every gate except the last is read by a later gate; output = last gate; computes f_G.
  Junk AND: an AND gate that is true on some input where f_G is false (equivalently, by
  monotonicity, true on some maximal independent set).
  Shard k (FIRSTJ=k): gates 0..k-1 are not junk ANDs, gate k is a junk AND, and some gate
  j in k+1..s-2 is a junk AND (JUNK2).
Symmetry breaking (position-safe): greedy topological order inside block [0,k) and inside
block (k,s) separately (key = (b, a, op), OR<AND); non-strict in block [0,k); in block (k,s)
non-strict except that two AND gates with the same inputs are excluded (merging such a pair,
and the copies it creates, keeps an AND twin of every removed junk AND inside (k,s); then pad
at the end with op(out, input of out)). For least sizes (no shard): strict everywhere.
Rows: the 16 edges (output 1) and the maximal independent sets (output 0).

Usage:
  junk_shard.py validate                 small-graph checks (pysat cadical195 + brute force)
  junk_shard.py validate_rs NMAX [--fam=P1,P2,MIS[,P1Q1]]  restriction bounds vs plain / brute
  junk_shard.py checkl --rsrec [--fam=...]     recompute LTABLE exactly (slow for 8 vertices)
  junk_shard.py checklb [--fam=...]            LTABLE entries are lower bounds (UNSAT below)
  junk_shard.py dimacs OUT.cnf S K [--nosb] [--rs=P1,P2,MIS --ltable]
  junk_shard.py cubes S K [same flags]         incremental CaDiCaL over cubes on gate K's inputs
  junk_shard.py decode SOLVER_OUT S K [same flags]
Shard 3 instance: dimacs s3.cnf 21 3 --rs=P1,P2,MIS --ltable ; solved with kissat 4.0.4.
"""
import itertools, json, os, sys, time

MAIN_N = 11
MAIN_EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8),
              (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
OPTS = {}
FAM = ['P1', 'P2', 'MIS']


def edge_fn(edges, x):
    return any(x[u] and x[v] for (u, v) in edges)


def maximal_independent_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    res = []
    for mask in range(1 << n):
        ins = [(mask >> i) & 1 for i in range(n)]
        if any(ins[u] and ins[v] for (u, v) in edges):
            continue
        if all(ins[i] or any(ins[v] for v in adj[i]) for i in range(n)):
            res.append(tuple(i for i in range(n) if ins[i]))
    return res


class CNF:
    def __init__(self):
        self.nv = 1
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


def atmost_seq(cnf, xs, k):
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


# ---------- restriction lower bounds (gate elimination), optional ----------
LTABLE = {
    '(2, ((0, 1),))': 1,
    '(3, ((0, 1), (0, 2)))': 2,
    '(4, ((0, 1), (2, 3)))': 3,
    '(3, ((0, 1), (0, 2), (1, 2)))': 4,
    '(4, ((0, 1), (0, 2), (1, 3)))': 4,
    '(4, ((0, 1), (0, 2), (0, 3), (1, 2)))': 5,
    '(5, ((0, 1), (0, 2), (1, 2), (3, 4)))': 6,
    '(5, ((0, 1), (0, 2), (0, 3), (1, 2), (3, 4)))': 7,
    '(5, ((0, 1), (0, 2), (1, 3), (2, 4), (3, 4)))': 7,
    '(6, ((0, 1), (0, 2), (0, 3), (1, 4), (2, 5)))': 7,
    '(6, ((0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5)))': 8,
    '(6, ((0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5)))': 8,
    '(6, ((0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)))': 9,
    '(7, ((0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6)))': 10,
    '(7, ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6), (3, 4)))': 11,
    '(7, ((0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5)))': 11,
    '(8, ((0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (5, 6), (5, 7), (6, 7)))': 12,
    '(8, ((0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (3, 5), (4, 6), (4, 7), (6, 7)))': 13,
    '(8, ((0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (3, 5), (3, 6), (4, 5), (4, 7), (6, 7)))': 11,
    '(8, ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6), (3, 4), (3, 7), (5, 7), (6, 7)))': 11,
}
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
    """Least size of a Monotone2 circuit for f_H (isolated vertices dropped), by SAT on the
    plain NF class (no junk constraint, strict greedy order), sizes 1,2,... ; exact."""
    if not edges:
        return 0
    k, c = canon_graph(edges)
    key = repr((k, c))
    if key in _LCACHE:
        return _LCACHE[key]
    if OPTS.get('ltable') and key in LTABLE:
        return LTABLE[key]
    if OPTS.get('lcache') and os.path.exists(OPTS['lcache']):
        with open(OPTS['lcache']) as f:
            disk = json.load(f)
        if key in disk:
            _LCACHE[key] = disk[key]
            return disk[key]
    for size in range(1, 60):
        cnf, meta = encode(k, list(c), size, None, rsflag=bool(OPTS.get('rsrec')))
        r, m = solve_pysat(cnf)
        if r:
            gates = decode(meta, m)
            assert verify(k, list(c), gates)
            break
    _LCACHE[key] = size
    if OPTS.get('lcache'):
        disk = {}
        if os.path.exists(OPTS['lcache']):
            with open(OPTS['lcache']) as f:
                disk = json.load(f)
        disk[key] = size
        with open(OPTS['lcache'], 'w') as f:
            json.dump(disk, f)
    return size


def restricted_least_size(n, edges, P, Q=()):
    """Lower bound for the least size of f restricted by x_P = 1, x_Q = 0 (P independent):
    OR_{a in A} x_a OR f_H, A = N(P) - Q, H = G - P - Q - N(P): |A| + L(H) if H has an edge
    (fix x_a = 0 one at a time: each kills >= 1 gate), else |A| - 1."""
    P = set(P)
    Q = set(Q)
    nb = set()
    for (u, v) in edges:
        if u in P:
            nb.add(v)
        if v in P:
            nb.add(u)
    A = nb - P - Q
    gone = P | Q | nb
    H = [(u, v) for (u, v) in edges if u not in gone and v not in gone]
    if H:
        return len(A) + least_size(H)
    return max(len(A) - 1, 0)


def restriction_family(n, edges, fam):
    es = set(tuple(sorted(e)) for e in edges)
    verts = sorted(set(v for e in edges for v in e))
    out = []
    if 'P1' in fam:
        for v in verts:
            out.append((v,))
    if 'P2' in fam:
        for u, v in itertools.combinations(verts, 2):
            if (u, v) not in es:
                out.append((u, v))
    if 'MIS' in fam:
        for m in maximal_independent_sets(n, edges):
            out.append(tuple(m))
    out = [(P_, ()) for P_ in out]
    if 'P1Q1' in fam:
        for v in verts:
            for w in verts:
                if w != v:
                    out.append(((v,), (w,)))
    return out


# ---------- encoder ----------
def encode(n, edges, s, firstj=None, junk2=True, order=True, rsflag=True):
    T, F = 1, -1
    mis = maximal_independent_sets(n, edges)
    rows = [((u, v), True) for (u, v) in edges] + [(m, False) for m in mis]
    misrows = list(range(len(edges), len(rows)))
    restr = []
    if rsflag and OPTS.get('rs'):
        for (P_, Q_) in restriction_family(n, edges, OPTS['rs']):
            L_ = restricted_least_size(n, edges, P_, Q_)
            if L_ > 0:
                restr.append((P_, Q_, L_))
        have = set(frozenset(st) for (st, _) in rows)
        for (P_, Q_, L_) in restr:
            for st in ([tuple(P_)] if P_ else []) + ([tuple(i for i in range(n) if i not in Q_)] if Q_ else []):
                if frozenset(st) not in have:
                    have.add(frozenset(st))
                    rows.append((st, edge_fn(edges, [i in st for i in range(n)])))
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
            cnf.add([-A[j][a], ulB[j](a + 1)])
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
    for j in range(s - 1):
        w = n + j
        cnf.add([X[k][w] for k in range(j + 1, s) for X in (A, B)])
    for w in sorted(set(v for e in edges for v in e)):
        cnf.add([X[k][w] for k in range(s) for X in (A, B)])
    if firstj is not None:
        k = firstj
        assert 0 <= k < s - 1
        for j in range(k):
            for t in misrows:
                cnf.add([-op[j], -g[j][t]])
        cnf.add([op[k]])
        cnf.add([g[k][t] for t in misrows])
        if junk2:
            ds = []
            for j in range(k + 1, s - 1):
                d = cnf.new()
                cnf.add([-d, op[j]])
                cnf.add([-d] + [g[j][t] for t in misrows])
                ds.append(d)
            cnf.add(ds)
    if order:
        if firstj is None:
            blocks = [(0, s, True)]
        else:
            blocks = [(0, firstj, False), (firstj + 1, s, 'noanddup')]
        for (lo, hi, strict) in blocks:
            for p in range(lo, hi):
                for q in range(p + 1, hi):
                    eqb = cnf.new()
                    eqab = cnf.new()
                    for beta in range(n + p):
                        cnf.add([-B[q][beta], -ulB[p](beta + 1)])
                        cnf.add([-B[q][beta], -B[p][beta], eqb])
                    for alpha in range(n + p):
                        cnf.add([-eqb, -A[q][alpha], -ulA[p](alpha + 1)])
                        cnf.add([-eqb, -A[q][alpha], -A[p][alpha], eqab])
                    if strict == 'noanddup':
                        cnf.add([-eqab, -op[p]])
                    elif strict:
                        cnf.add([-eqab, -op[p]])
                        cnf.add([-eqab, op[q]])
                    else:
                        cnf.add([-eqab, -op[p], op[q]])
    if restr:
        idx = {frozenset(st): t for t, (st, _) in enumerate(rows)}
        for (P_, Q_, L_) in restr:
            t0 = idx[frozenset(P_)] if P_ else None
            t1 = idx[frozenset(i for i in range(n) if i not in Q_)] if Q_ else None
            es = []
            for j in range(s):
                e = cnf.new()
                if t0 is not None:
                    cnf.add([-va[j][t0], e])
                    cnf.add([-vb[j][t0], e])
                if t1 is not None:
                    cnf.add([va[j][t1], e])
                    cnf.add([vb[j][t1], e])
                es.append(e)
            atmost_seq(cnf, es, s - L_)
    meta = dict(n=n, s=s, op=op, A=A, B=B, rows=rows, nrestr=len(restr))
    return cnf, meta


def decode(meta, model_set):
    n, s = meta['n'], meta['s']
    gates = []
    for j in range(s):
        sa = [i for i, v in enumerate(meta['A'][j]) if v in model_set]
        sb = [i for i, v in enumerate(meta['B'][j]) if v in model_set]
        assert len(sa) == 1 and len(sb) == 1 and sa[0] < sb[0], (sa, sb)
        gates.append(('AND' if meta['op'][j] in model_set else 'OR', [sa[0], sb[0]]))
    return gates


def lean_eval(gates, output, x):
    """Mirror of Circuit.wires / Circuit.eval: missing wires read false, AND [] = true."""
    w = list(x)
    for (o, inp) in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        w.append(all(vals) if o == 'AND' else any(vals))
    return (w[output] if output < len(w) else False), w


def verify(n, edges, gates, output=None):
    if output is None:
        output = n + len(gates) - 1
    for mask in range(1 << n):
        x = [bool((mask >> i) & 1) for i in range(n)]
        if lean_eval(gates, output, x)[0] != edge_fn(edges, x):
            return False
    return True


def junk_profile(n, edges, gates):
    """Positions of junk AND gates, computed on all 2^n inputs."""
    junk = set()
    for mask in range(1 << n):
        x = [bool((mask >> i) & 1) for i in range(n)]
        if edge_fn(edges, x):
            continue
        _, w = lean_eval(gates, n + len(gates) - 1, x)
        for j, (o, _) in enumerate(gates):
            if o == 'AND' and w[n + j]:
                junk.add(j)
    return sorted(junk)


def solve_pysat(cnf, name='cadical195'):
    from pysat.solvers import Solver
    with Solver(name=name, bootstrap_with=cnf.clauses) as sv:
        r = sv.solve()
        m = sv.get_model() if r else None
    return r, (set(l for l in m if l > 0) if m else None)


# ---------- brute force (independent of the encoder) ----------
BRUTE_C = r"""#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
/* brute n s u1 v1 u2 v2 ... : enumerate all NF circuits (exactly s gates, AND/OR of two
   distinct earlier wires, every non-last gate read later, output last); print whether any
   computes f, and for each k whether some circuit computing f has lowest junk AND at k and
   another junk AND above it. Truth tables on 2^n <= 64 inputs. */
static int n, s;
static uint64_t tt[64], f, nf;
static int isand[64], used[64];
static int found[64], anyf;
static void rec(int j) {
  if (j == s) {
    if (tt[n + s - 1] != f) return;
    for (int q = 0; q < s - 1; q++) if (!used[n + q]) return;
    anyf = 1;
    int first = -1, cnt = 0;
    for (int q = 0; q < s; q++) if (isand[q] && (tt[n + q] & nf)) { if (first < 0) first = q; cnt++; }
    if (cnt >= 2) found[first] = 1;
    return;
  }
  int unused = 0;
  for (int q = 0; q < j; q++) if (!used[n + q]) unused++;
  int rafter = s - 1 - j;
  for (int b = 0; b < n + j; b++)
    for (int a = 0; a < b; a++) {
      int nu = unused - ((a >= n && !used[a]) ? 1 : 0) - ((b >= n && !used[b]) ? 1 : 0) + 1;
      if (rafter >= 1 && nu > rafter + 1) continue;
      used[a]++; used[b]++;
      for (int o = 0; o < 2; o++) {
        isand[j] = o;
        tt[n + j] = o ? (tt[a] & tt[b]) : (tt[a] | tt[b]);
        rec(j + 1);
      }
      used[a]--; used[b]--;
    }
}
int main(int argc, char **argv) {
  n = atoi(argv[1]); s = atoi(argv[2]);
  int N = 1 << n;
  uint64_t full = (N == 64) ? ~0ULL : ((1ULL << N) - 1);
  for (int i = 0; i < n; i++) { tt[i] = 0; for (int m = 0; m < N; m++) if ((m >> i) & 1) tt[i] |= 1ULL << m; }
  f = 0;
  for (int m = 0; m < N; m++) {
    int v = 0;
    for (int e = 3; e + 1 < argc; e += 2) { int u = atoi(argv[e]), w = atoi(argv[e + 1]); if (((m >> u) & 1) && ((m >> w) & 1)) v = 1; }
    if (v) f |= 1ULL << m;
  }
  nf = full ^ f;
  rec(0);
  printf("%d", anyf);
  for (int k = 0; k < s; k++) if (found[k]) printf(" %d", k);
  printf("\n");
  return 0;
}
"""


def brute_shards(n, edges, s):
    """All NF circuits of exactly s gates, no ordering (C brute force, independent of the
    encoder): returns (any circuit computes f, set of k such that some circuit computing f
    has lowest junk AND at k and another junk AND above it)."""
    import subprocess, tempfile
    d = os.path.join(tempfile.gettempdir(), 'junk_shard_brute_%d' % os.getpid())
    exe = os.path.join(d, 'brute')
    if not os.path.exists(exe):
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, 'brute.c'), 'w') as fh:
            fh.write(BRUTE_C)
        subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(d, 'brute.c')])
    args = [exe, str(n), str(s)] + [str(z) for e in edges for z in e]
    out = subprocess.check_output(args).decode().split()
    return out[0] == '1', set(int(z) for z in out[1:])


def sat_shard(n, edges, s, k, order=True):
    cnf, meta = encode(n, edges, s, k, junk2=True, order=order)
    r, m = solve_pysat(cnf)
    if r:
        gates = decode(meta, m)
        assert verify(n, edges, gates), gates
        js = junk_profile(n, edges, gates)
        assert len(js) >= 2 and js[0] == k, (gates, js)
    return bool(r)


def min_size_sat(n, edges, smax, order=True):
    res = {}
    for s in range(1, smax + 1):
        cnf, meta = encode(n, edges, s, None, order=order)
        r, m = solve_pysat(cnf)
        res[s] = r
        if r:
            gates = decode(meta, m)
            assert verify(n, edges, gates)
            return s, gates, res
    return None, None, res


def validate():
    t0 = time.time()
    allok = True
    for name, n, edges, known in [
            ('P4', 4, [(0, 1), (1, 2), (2, 3)], 4),
            ('K13', 4, [(0, 1), (0, 2), (0, 3)], 3),
            ('C5', 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 7),
            ('P5', 5, [(0, 1), (1, 2), (2, 3), (3, 4)], 5),
            ('C4', 4, [(0, 1), (1, 2), (2, 3), (3, 0)], 3),
            ('K3', 3, [(0, 1), (1, 2), (0, 2)], 4)]:
        for order in (True, False):
            s, gates, res = min_size_sat(n, edges, known + 1, order=order)
            ok = s == known and all(res[q] is False for q in range(1, known))
            allok &= ok
            print('min size %s order=%s: %s (known %d) %s %s' % (name, order, s, known,
                  'OK' if ok else 'MISMATCH', gates), flush=True)
    cases = [('P4', 4, [(0, 1), (1, 2), (2, 3)], [4, 5, 6]),
             ('K13', 4, [(0, 1), (0, 2), (0, 3)], [4, 5, 6]),
             ('C4', 4, [(0, 1), (1, 2), (2, 3), (3, 0)], [4, 5, 6]),
             ('2K2', 4, [(0, 1), (2, 3)], [4, 5, 6]),
             ('paw', 4, [(0, 1), (1, 2), (0, 2), (2, 3)], [4, 5, 6]),
             ('P3+K1', 4, [(0, 1), (1, 2)], [4, 5, 6]),
             ('K4-e', 4, [(0, 1), (1, 2), (0, 2), (1, 3), (2, 3)], [5, 6]),
             ('P5', 5, [(0, 1), (1, 2), (2, 3), (3, 4)], [5, 6]),
             ('K14', 5, [(0, 1), (0, 2), (0, 3), (0, 4)], [5, 6]),
             ('bull', 5, [(0, 1), (1, 2), (0, 2), (1, 3), (2, 4)], [6]),
             ('P4+K1', 5, [(0, 1), (1, 2), (2, 3)], [5, 6])]
    for name, n, edges, sizes in cases:
        for s in sizes:
            tb = time.time()
            anyf, found = brute_shards(n, edges, s)
            tb = time.time() - tb
            for k in range(s - 1):
                a = sat_shard(n, edges, s, k, order=True)
                b = sat_shard(n, edges, s, k, order=False)
                exp = k in found
                ok = (a == exp) and (b == exp)
                allok &= ok
                print('shard %s s=%d k=%d: brute=%s sat_sb=%s sat_nosb=%s %s' %
                      (name, s, k, exp, a, b, 'OK' if ok else 'MISMATCH'), flush=True)
            print('  (%s s=%d: brute %.1fs, any circuit: %s, shards with a circuit: %s)' %
                  (name, s, tb, anyf, sorted(found)), flush=True)
    print('validate: all ok = %s, %.1fs' % (allok, time.time() - t0))
    return allok


def checkl():
    """Recompute every LTABLE entry by SAT (exact least size, sizes 1,2,... in the plain NF
    class; with --rsrec the smaller subgraphs' bounds are used recursively, also recomputed).
    A table value is sound if it is <= the computed least size."""
    OPTS.clear()
    OPTS['rs'] = set(FAM)
    OPTS['rsrec'] = '--rsrec' in sys.argv
    allok = True
    for key, val in sorted(LTABLE.items(), key=lambda kv: (len(kv[0]), kv[1])):
        k, c = eval(key)
        t0 = time.time()
        L = least_size(list(c))
        ok = val <= L
        allok &= ok
        print('%s table=%d computed=%d %s %.1fs' % (key, val, L, 'OK' if ok else 'BAD', time.time() - t0), flush=True)
    print('checkl all ok:', allok)


def graphs_upto_iso(n):
    allpairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    seen = set()
    out = []
    for m in range(1, len(allpairs) + 1):
        for es in itertools.combinations(allpairs, m):
            canon = min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in es))
                        for p in itertools.permutations(range(n)))
            if canon in seen:
                continue
            seen.add(canon)
            out.append(list(es))
    return out


def validate_rs(nmax):
    """Restriction bounds (P1,P2,MIS, recursive): least sizes with and without them agree on
    every graph with at most nmax vertices; shard answers with them agree with brute force."""
    t0 = time.time()
    allok = True
    for n in range(2, nmax + 1):
        for edges in graphs_upto_iso(n):
            OPTS.clear()
            _LCACHE.clear()
            s0, g0, r0 = min_size_sat(n, edges, 20)
            OPTS['rs'] = set(FAM)
            OPTS['rsrec'] = True
            _LCACHE.clear()
            s1, g1, r1 = min_size_sat(n, edges, 20)
            ok = s0 == s1
            allok &= ok
            if not ok:
                print('MISMATCH min size', n, edges, s0, s1, flush=True)
    print('rs min-size check up to n=%d: %s (%.1fs)' % (nmax, allok, time.time() - t0), flush=True)
    for name, n, edges, sizes in [('P4', 4, [(0, 1), (1, 2), (2, 3)], [6]),
                                  ('K13', 4, [(0, 1), (0, 2), (0, 3)], [6]),
                                  ('C4', 4, [(0, 1), (1, 2), (2, 3), (3, 0)], [6]),
                                  ('2K2', 4, [(0, 1), (2, 3)], [6]),
                                  ('P3+K1', 4, [(0, 1), (1, 2)], [5, 6]),
                                  ('P4+K1', 5, [(0, 1), (1, 2), (2, 3)], [6]),
                                  ('P5', 5, [(0, 1), (1, 2), (2, 3), (3, 4)], [6]),
                                  ('bull', 5, [(0, 1), (1, 2), (0, 2), (1, 3), (2, 4)], [6])]:
        for s in sizes:
            anyf, found = brute_shards(n, edges, s)
            for k in range(s - 1):
                OPTS.clear()
                OPTS['rs'] = set(FAM)
                OPTS['rsrec'] = True
                _LCACHE.clear()
                a = sat_shard(n, edges, s, k, order=True)
                ok = a == (k in found)
                allok &= ok
                print('rs shard %s s=%d k=%d: brute=%s sat_rs=%s %s' % (name, s, k, k in found, a,
                      'OK' if ok else 'MISMATCH'), flush=True)
    OPTS.clear()
    print('validate_rs: all ok = %s, %.1fs' % (allok, time.time() - t0))
    return allok


def checklb():
    """Soundness check of LTABLE as lower bounds: for every entry with value L, the plain NF
    class (strict order, restriction bounds of the family FAM computed recursively, no table)
    is UNSAT at every size 1..L-1."""
    OPTS.clear()
    OPTS['rs'] = set(FAM)
    OPTS['rsrec'] = True
    allok = True
    for key, val in sorted(LTABLE.items(), key=lambda kv: (len(kv[0]), kv[1])):
        k, c = eval(key)
        t0 = time.time()
        res = []
        for size in range(val - 1, 0, -1):
            cnf, meta = encode(k, list(c), size, None)
            r, m = solve_pysat(cnf)
            res.append(r)
        ok = not any(res)
        allok &= ok
        print('%s table=%d UNSAT at all sizes below: %s %.1fs' % (key, val, ok, time.time() - t0),
              flush=True)
    print('checklb all ok:', allok)
    return allok


def parse_flags(argv):
    for a in argv:
        if a.startswith('--rs='):
            OPTS['rs'] = set(a[5:].split(','))
        if a.startswith('--lcache='):
            OPTS['lcache'] = a[9:]
        if a == '--ltable':
            OPTS['ltable'] = True


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
        sys.exit(0 if validate() else 1)
    elif cmd in ('validate_rs', 'checkl', 'checklb') and any(a.startswith('--fam=') for a in sys.argv):
        FAM[:] = [a for a in sys.argv if a.startswith('--fam=')][0][6:].split(',')
        sys.argv = [a for a in sys.argv if not a.startswith('--fam=')]
        main()
    elif cmd == 'validate_rs':
        sys.exit(0 if validate_rs(int(sys.argv[2]) if len(sys.argv) > 2 else 5) else 1)
    elif cmd == 'checkl':
        checkl()
    elif cmd == 'checklb':
        sys.exit(0 if checklb() else 1)
    elif cmd == 'dimacs':
        out, s, k = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        parse_flags(sys.argv[5:])
        cnf, meta = encode(MAIN_N, MAIN_EDGES, s, k, junk2=True, order='--nosb' not in sys.argv)
        write_dimacs(cnf, out)
        print('wrote %s: s=%d k=%d vars=%d clauses=%d rows=%d restrictions=%d' %
              (out, s, k, cnf.nv, len(cnf.clauses), len(meta['rows']), meta['nrestr']))
    elif cmd == 'cubes':
        # cubes S K [flags]: incremental CaDiCaL (pysat cadical195) over the cubes
        # 'gate K reads wires (a, b)', all a < b < n+K; every cube UNSAT => instance UNSAT.
        s, k = int(sys.argv[2]), int(sys.argv[3])
        parse_flags(sys.argv[4:])
        cnf, meta = encode(MAIN_N, MAIN_EDGES, s, k, junk2=True, order='--nosb' not in sys.argv)
        from pysat.solvers import Solver
        t0 = time.time()
        pairs = [(a, b) for b in range(MAIN_N + k) for a in range(b)]
        print('cubes: %d, vars=%d clauses=%d' % (len(pairs), cnf.nv, len(cnf.clauses)), flush=True)
        nunsat = 0
        with Solver(name='cadical195', bootstrap_with=cnf.clauses) as sv:
            for (a, b) in pairs:
                tc = time.time()
                r = sv.solve(assumptions=[meta['A'][k][a], meta['B'][k][b]])
                print('cube (%d,%d): %s %.1fs total %.1fs' % (a, b, 'SAT' if r else 'UNSAT',
                      time.time() - tc, time.time() - t0), flush=True)
                if r:
                    m = set(l for l in sv.get_model() if l > 0)
                    gates = decode(meta, m)
                    print('gates:', gates)
                    print('computes f on all 2048 inputs:', verify(MAIN_N, MAIN_EDGES, gates))
                    print('junk AND positions:', junk_profile(MAIN_N, MAIN_EDGES, gates))
                    break
                nunsat += 1
        print('cubes done: %d/%d UNSAT, %.1fs' % (nunsat, len(pairs), time.time() - t0), flush=True)
    elif cmd == 'decode':
        sol, s, k = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        parse_flags(sys.argv[5:])
        cnf, meta = encode(MAIN_N, MAIN_EDGES, s, k, junk2=True, order='--nosb' not in sys.argv)
        lits = []
        with open(sol) as f:
            for line in f:
                if line.startswith('v '):
                    lits += [int(z) for z in line.split()[1:]]
        m = set(l for l in lits if l > 0)
        gates = decode(meta, m)
        print('gates:', gates)
        print('computes f on all 2048 inputs:', verify(MAIN_N, MAIN_EDGES, gates))
        print('junk AND positions:', junk_profile(MAIN_N, MAIN_EDGES, gates))
    else:
        print(__doc__)


if __name__ == '__main__':
    main()
