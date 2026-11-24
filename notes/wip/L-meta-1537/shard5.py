"""L-meta-1537 shard 5 (three leaking lines in a triangle), q = 3.

Part A: PG(2,3), incidence checks, arc count (560).
Part B: exact Python model of the Lean statement's semantics (Circuit.wires, supports,
        normalized hypothesis, outputs right on arcs, K_l / W_l / leak / B / H) and checks
        on the plain 39-gate circuit and on a hand-built circuit with one B-line.
Part C: SAT relaxation at the support level (values on unit vectors only):
        gates AND/OR fan-in <= 2 (absent slots, wires, earlier gates, or a not-yet-existing
        wire which reads false), three triangle lines each have an output gate with support
        exactly the line, and at most 4 gates are not H-eligible (H-eligible = support of
        size >= 2 inside a non-triangle line). Any shard-5 counterexample with n gates is a
        model (3|B| + 2|H| > 2n with |B| = 3 forces n - |H| <= 4). UNSAT for every n tried.
"""
import itertools, sys, time
from pysat.formula import IDPool, CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

Q = 3
N = Q * Q + Q + 1

def norm(v):
    for c in v:
        if c % 3:
            inv = 1 if c % 3 == 1 else 2
            return tuple((inv * x) % 3 for x in v)
    return None

PTS = sorted({norm(v) for v in itertools.product(range(3), repeat=3) if any(v)})
LNS = PTS
assert len(PTS) == N
INC = [[sum(a * b for a, b in zip(PTS[p], LNS[l])) % 3 == 0 for l in range(N)] for p in range(N)]
LINE = [frozenset(p for p in range(N) if INC[p][l]) for l in range(N)]
assert all(len(L) == Q + 1 for L in LINE)
for p1 in range(N):
    for p2 in range(p1 + 1, N):
        assert sum(1 for l in range(N) if INC[p1][l] and INC[p2][l]) == 1

def is_arc(S):
    return all(len(S & L) <= 2 for L in LINE)

ARCS = [frozenset(p for p in range(N) if m >> p & 1) for m in range(1 << N)]
ARCS = [S for S in ARCS if is_arc(S)]
assert len(ARCS) == 560, len(ARCS)

def line_through(a, b):
    return next(l for l in range(N) if a in LINE[l] and b in LINE[l])

TRI = None
for t in itertools.combinations(range(N), 3):
    if not (LINE[t[0]] & LINE[t[1]] & LINE[t[2]]):
        TRI = t
        break
assert TRI is not None

AND, OR = 'and', 'or'

def wires(gates, x):
    w = list(x)
    for op, ins in gates:
        vals = [w[i] if i < len(w) else False for i in ins]
        w.append(all(vals) if op == AND else any(vals))
    return w

def getD(w, i):
    return w[i] if i < len(w) else False

def unit(u):
    return [k == u for k in range(N)]

def supp_all(gates):
    W = [wires(gates, unit(u)) for u in range(N)]
    return lambda i: frozenset(u for u in range(N) if getD(W[u], i))

def analyse(gates, out):
    G = len(gates)
    assert all(op in (AND, OR) and len(ins) <= 2 for op, ins in gates)
    sp = supp_all(gates)
    allx = [[bool(m >> p & 1) for p in range(N)] for m in range(1 << N)]
    allw = [wires(gates, x) for x in allx]
    for k in range(G):
        s = sp(N + k)
        if len(s) <= 1:
            for x, w in zip(allx, allw):
                assert getD(w, N + k) == any(x[v] for v in s), ('not normalized', k)
    for l in range(N):
        for S in ARCS:
            x = [p in S for p in range(N)]
            assert getD(wires(gates, x), out[l]) == bool(S & LINE[l]), ('output wrong', l, S)
    def K(l):
        Kl = set()
        k0 = out[l] - N
        if out[l] >= N and k0 < G and sp(out[l]) <= LINE[l]:
            Kl.add(k0)
        changed = True
        while changed:
            changed = False
            for k1 in list(Kl):
                for i in gates[k1][1]:
                    if i >= N:
                        k2 = i - N
                        if k2 < k1 and sp(N + k2) <= LINE[l] and k2 not in Kl:
                            Kl.add(k2)
                            changed = True
        return Kl
    def Wb(l):
        return {w for k in K(l) if gates[k][0] == AND for w in gates[k][1]
                if w < N + k and not sp(w) <= LINE[l]}
    def leak(l):
        ws = Wb(l)
        return any(not (y & LINE[l]) and all(sp(w) & y for w in ws) for y in ARCS)
    LK = [leak(l) for l in range(N)]
    B = [l for l in range(N) if not LK[l]]
    H = [k for k in range(G) if len(sp(N + k)) >= 2 and any(LK[l] and sp(N + k) <= LINE[l] for l in range(N))]
    return B, H, [sorted(Wb(l)) for l in range(N)]

def plain():
    gates, out = [], []
    for l in range(N):
        p = sorted(LINE[l])
        gates.append((OR, [p[0], p[1]]))
        gates.append((OR, [N + len(gates) - 1, p[2]]))
        gates.append((OR, [N + len(gates) - 1, p[3]]))
        out.append(N + len(gates) - 1)
    return gates, out

def one_b_line():
    gates, out = plain()
    l = 0
    m = next(mm for mm in range(N) if mm != l)
    a, b, c = sorted(LINE[m] - LINE[l])
    base = len(gates)
    gates.append((AND, [a, 10 ** 6]))
    gates.append((AND, [b, N + base]))
    gates.append((AND, [c, N + base + 1]))
    p = sorted(LINE[l])
    gates[0] = (OR, [p[0], p[1]])
    gates.append((OR, [p[3], N + base + 2]))
    gates.append((OR, [N + 1, N + base + 3]))
    out[l] = N + len(gates) - 1
    return gates, out

def partB():
    g, o = plain()
    B, H, _ = analyse(g, o)
    print('plain: gates', len(g), 'B', B, '|H|', len(H), 'q|B|+2|H| =', Q * len(B) + 2 * len(H), '<= 2|gates| =', 2 * len(g))
    assert B == [] and len(H) == 39
    g, o = one_b_line()
    B, H, W = analyse(g, o)
    print('one-B-line example: gates', len(g), 'B', B, 'W', W[0], '|H|', len(H), 'q|B|+2|H| =', Q * len(B) + 2 * len(H), '<= 2|gates| =', 2 * len(g))
    assert B == [0]

def build(n, outs_lines, max_nonelig, need_all=False, extra=()):
    vp = IDPool()
    cnf = CNF()
    op = [vp.id(('op', k)) for k in range(n)]
    S = [[vp.id(('S', k, u)) for u in range(N)] for k in range(n)]
    nonT = [m for m in range(N) if m not in outs_lines]
    for k in range(n):
        srcs = ['ABS', 'FALSE'] + [('X', p) for p in range(N)] + [('G', j) for j in range(k)]
        vals = []
        for s in range(2):
            sel = {src: vp.id(('sel', k, s, src)) for src in srcs}
            for cl in CardEnc.equals(list(sel.values()), 1, vpool=vp, encoding=EncType.seqcounter).clauses:
                cnf.append(cl)
            val = [vp.id(('val', k, s, u)) for u in range(N)]
            for u in range(N):
                v = val[u]
                cnf.append([-sel['ABS'], -v, op[k]]); cnf.append([-sel['ABS'], v, -op[k]])
                cnf.append([-sel['FALSE'], -v])
                for p in range(N):
                    cnf.append([-sel[('X', p)], v if p == u else -v])
                for j in range(k):
                    cnf.append([-sel[('G', j)], -v, S[j][u]]); cnf.append([-sel[('G', j)], v, -S[j][u]])
            vals.append(val)
        for u in range(N):
            a, b, z = vals[0][u], vals[1][u], S[k][u]
            cnf.append([-op[k], -z, a]); cnf.append([-op[k], -z, b]); cnf.append([-op[k], z, -a, -b])
            cnf.append([op[k], z, -a]); cnf.append([op[k], z, -b]); cnf.append([op[k], -z, a, b])
    lines = list(range(N)) if need_all else list(outs_lines) + list(extra)
    for l in lines:
        o = [vp.id(('out', l, k)) for k in range(n)]
        cnf.append(o)
        for k in range(n):
            for u in range(N):
                cnf.append([-o[k], S[k][u] if u in LINE[l] else -S[k][u]])
    elig = [vp.id(('elig', k)) for k in range(n)]
    for k in range(n):
        for u in range(N):
            cnf.append([-elig[k]] + [S[k][v] for v in range(N) if v != u])
        subs = []
        for m in nonT:
            sv = vp.id(('sub', k, m))
            subs.append(sv)
            for u in range(N):
                if u not in LINE[m]:
                    cnf.append([-sv, -S[k][u]])
        cnf.append([-elig[k]] + subs)
    if max_nonelig is not None:
        for cl in CardEnc.atmost([-e for e in elig], max_nonelig, vpool=vp, encoding=EncType.seqcounter).clauses:
            cnf.append(cl)
    return cnf, vp, elig

def solve(cnf, name='cadical195'):
    t = time.time()
    with Solver(name=name, bootstrap_with=cnf.clauses) as s:
        r = s.solve()
        m = s.get_model() if r else None
    return r, time.time() - t, m

def partC(nmax, need_all=False):
    print('triangle lines', TRI, [sorted(LINE[l]) for l in TRI], 'need_all' if need_all else 'triangle outputs only')
    total = 0.0
    for n in range(1, nmax + 1):
        cnf, vp, _ = build(n, TRI, 4, need_all)
        r, dt, _ = solve(cnf)
        total += dt
        print(f'n={n} vars={vp.top} clauses={len(cnf.clauses)} nonelig<=4: {"SAT" if r else "UNSAT"} {dt:.2f}s', flush=True)
        assert not r
    print(f'all UNSAT up to n={nmax}, solver time {total:.1f}s')

def decode(n, vp, m):
    pos = set(l for l in m if l > 0)
    gates = []
    for k in range(n):
        o = AND if vp.id(('op', k)) in pos else OR
        ins = []
        for s in range(2):
            srcs = ['ABS', 'FALSE'] + [('X', p) for p in range(N)] + [('G', j) for j in range(k)]
            src = [x for x in srcs if vp.id(('sel', k, s, x)) in pos]
            assert len(src) == 1
            x = src[0]
            if x == 'FALSE':
                ins.append(10 ** 6)
            elif x != 'ABS':
                ins.append(x[1] if x[0] == 'X' else N + x[1])
        gates.append((o, ins))
    sp = supp_all(gates)
    for k in range(n):
        assert sp(N + k) == frozenset(u for u in range(N) if vp.id(('S', k, u)) in pos)
    nonT = [l for l in range(N) if l not in TRI]
    elig = [len(sp(N + k)) >= 2 and any(sp(N + k) <= LINE[l] for l in nonT) for k in range(n)]
    return gates, sp, elig

def check_model(n, vp, m, lines, bound):
    gates, sp, elig = decode(n, vp, m)
    for l in lines:
        assert any(sp(N + k) == LINE[l] for k in range(n)), ('no output for line', l)
    ne = elig.count(False)
    assert bound is None or ne <= bound
    return gates, ne

def validate():
    for n in range(1, 10):
        cnf, vp, _ = build(n, TRI, None)
        r, dt, m = solve(cnf)
        print(f'V1: n={n} triangle outputs only, no bound on non-eligible gates: {"SAT" if r else "UNSAT"} {dt:.2f}s', flush=True)
        if r:
            g, ne = check_model(n, vp, m, TRI, None)
            print('    decoded model re-evaluated with the exact wires semantics: ok; gates', g, 'non-eligible', ne)
            break
    other = next(l for l in range(N) if l not in TRI)
    for n, extra, b in ((12, (other,), 9),):
        cnf, vp, _ = build(n, TRI, b, extra=extra)
        r, dt, m = solve(cnf)
        msg = ''
        if r:
            g, ne = check_model(n, vp, m, list(TRI) + list(extra), b)
            msg = f'decoded ok, non-eligible {ne}'
        print(f'V2: n={n} outputs for triangle + line {other}, non-eligible <= {b}: {"SAT" if r else "UNSAT"} {dt:.2f}s {msg}', flush=True)
    cnf, vp, _ = build(39, TRI, 9, need_all=True)
    r, dt, m = solve(cnf)
    msg = ''
    if r:
        g, ne = check_model(39, vp, m, range(N), 9)
        msg = f'decoded ok, non-eligible {ne}'
    print(f'V3: n=39 outputs for all 13 lines, non-eligible <= 9: {"SAT" if r else "UNSAT"} {dt:.2f}s {msg}', flush=True)

if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if what in ('A', 'all'):
        print('PG(2,3): 13 points, 13 lines, 4 points per line, unique line through 2 points; arcs =', len(ARCS))
    if what in ('B', 'all'):
        partB()
    if what in ('V', 'all'):
        validate()
    if what in ('C', 'all'):
        partC(int(sys.argv[2]) if len(sys.argv) > 2 else 39)
    if what == 'CF':
        partC(int(sys.argv[2]) if len(sys.argv) > 2 else 39, need_all=True)
