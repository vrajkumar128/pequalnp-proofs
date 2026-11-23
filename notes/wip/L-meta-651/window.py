import sys, time, random, itertools
from pysat.solvers import Solver

N = 10
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
FULL = (1 << 1024) - 1

def var_tt(v):
    r = 0
    for t in range(1024):
        if (t >> v) & 1:
            r |= 1 << t
    return r

XT = [var_tt(v) for v in range(N)]
FTT = 0
for a, b in EDGES:
    FTT |= XT[a] & XT[b]

def tts(circ):
    w = list(XT)
    for op, a, b in circ:
        if op == 'and': w.append(w[a] & w[b])
        elif op == 'or': w.append(w[a] | w[b])
        else: w.append(FULL ^ w[a])
    return w

def ok(circ):
    return tts(circ)[-1] == FTT

def parse_sa(path):
    circs = []
    lines = [l.split() for l in open(path)]
    i = 0
    while i < len(lines):
        p = lines[i]
        if p and p[0] == 'FOUND':
            S = int(p[1].split('=')[1])
            c = [(q[0], int(q[1]), int(q[2])) for q in lines[i+1:i+1+S]]
            circs.append(c)
            i += 1 + S
        else:
            i += 1
    return circs

def clean(circ):
    s = len(circ)
    used = [False] * (N + s)
    used[N + s - 1] = True
    for i in range(s - 1, -1, -1):
        if used[N + i]:
            op, a, b = circ[i]
            used[a] = True
            if op != 'not':
                used[b] = True
    newidx = list(range(N))
    out = []
    for i in range(s):
        if used[N + i]:
            op, a, b = circ[i]
            out.append((op, newidx[a], newidx[b] if op != 'not' else newidx[a]))
            newidx.append(N + len(out) - 1)
        else:
            newidx.append(None)
    return out

def synth_window(n_in, rows, n_out, k, timeout_conf=None):
    S = Solver(name='cadical195')
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    W = n_in + k
    L = [[new() for _ in range(n_in + i)] for i in range(k)]
    R = [[new() for _ in range(n_in + i)] for i in range(k)]
    TA = [new() for _ in range(k)]; TO = [new() for _ in range(k)]; TN = [new() for _ in range(k)]
    O = [[new() for _ in range(W)] for _ in range(n_out)]
    def eo(xs):
        S.add_clause(list(xs))
        for a in range(len(xs)):
            for b in range(a):
                S.add_clause([-xs[a], -xs[b]])
    for i in range(k):
        g = n_in + i
        eo(L[i]); eo(R[i]); eo([TA[i], TO[i], TN[i]])
        for j in range(g):
            for kk in range(j):
                S.add_clause([-L[i][j], -R[i][kk]])
            S.add_clause([-TN[i], -L[i][j], R[i][j]])
            S.add_clause([TN[i], -L[i][j], -R[i][j]])
    for o in range(n_out):
        eo(O[o])
    for i in range(k):
        g = n_in + i
        S.add_clause([R[i2][g] for i2 in range(i + 1, k)] + [L[i2][g] for i2 in range(i + 1, k)] + [O[o][g] for o in range(n_out)])
    for (inp, outv) in rows:
        V = {}
        for i in range(k):
            g = n_in + i
            v = new(); V[g] = v
            A = new(); B = new()
            for j in range(g):
                if j < n_in:
                    for X, Y in ((L[i][j], A), (R[i][j], B)):
                        S.add_clause([-X, Y] if inp[j] else [-X, -Y])
                else:
                    for X, Y in ((L[i][j], A), (R[i][j], B)):
                        S.add_clause([-X, -Y, V[j]]); S.add_clause([-X, Y, -V[j]])
            S.add_clause([-TA[i], -A, -B, v]); S.add_clause([-TA[i], A, -v]); S.add_clause([-TA[i], B, -v])
            S.add_clause([-TO[i], A, B, -v]); S.add_clause([-TO[i], -A, v]); S.add_clause([-TO[i], -B, v])
            S.add_clause([-TN[i], A, v]); S.add_clause([-TN[i], -A, -v])
        for o in range(n_out):
            for w in range(W):
                if w < n_in:
                    if bool(inp[w]) != bool(outv[o]):
                        S.add_clause([-O[o][w]])
                else:
                    S.add_clause([-O[o][w], V[w] if outv[o] else -V[w]])
    r = S.solve()
    if not r:
        S.delete()
        return None
    m = set(x for x in S.get_model() if x > 0)
    gates = []
    for i in range(k):
        j = [a for a in range(n_in + i) if L[i][a] in m][0]
        kk = [a for a in range(n_in + i) if R[i][a] in m][0]
        op = 'and' if TA[i] in m else ('or' if TO[i] in m else 'not')
        gates.append((op, j, kk))
    outs = [[w for w in range(W) if O[o][w] in m][0] for o in range(n_out)]
    S.delete()
    return gates, outs

def try_window(circ, Wset, max_in=8, max_out=3):
    s = len(circ)
    Wl = sorted(Wset)
    Ws = set(Wl)
    readers = {}
    for i, (op, a, b) in enumerate(circ):
        ins = [a] if op == 'not' else [a, b]
        for x in ins:
            readers.setdefault(x, set()).add(N + i)
    ins = []
    for g in Wl:
        op, a, b = circ[g - N]
        for x in ([a] if op == 'not' else [a, b]):
            if x not in Ws and x not in ins:
                ins.append(x)
    outs = [g for g in Wl if (g == N + s - 1) or any(r not in Ws for r in readers.get(g, ()))]
    if len(ins) > max_in or len(outs) > max_out or not outs:
        return None
    for g in Wl:
        for r in readers.get(g, ()):
            if r not in Ws:
                pass
    # convexity: no path from W out of W and back into W
    minW = min(Wl)
    reach = set()
    for g in range(minW, N + s):
        if g in Ws:
            continue
        op, a, b = circ[g - N]
        src = [a] if op == 'not' else [a, b]
        if any((x in Ws) or (x in reach) for x in src):
            reach.add(g)
    for g in Wl:
        op, a, b = circ[g - N]
        src = [a] if op == 'not' else [a, b]
        if any(x in reach for x in src):
            return None
    T = tts(circ)
    rows = {}
    for t in range(1024):
        key = tuple((T[x] >> t) & 1 for x in ins)
        val = tuple((T[g] >> t) & 1 for g in outs)
        rows[key] = val
    k = len(Wl) - 1
    res = synth_window(len(ins), list(rows.items()), len(outs), k)
    if res is None:
        return None
    gates, outsel = res
    return ins, outs, gates, outsel

def splice(circ, Wset, ins, outs, gates, outsel):
    s = len(circ)
    Ws = set(Wset)
    # new order: place all non-W gates that are not reachable from W before? simpler: topological rebuild
    nodes = {}
    for i, (op, a, b) in enumerate(circ):
        g = N + i
        if g in Ws:
            continue
        nodes[('o', g)] = (op, a, b)
    loc = {}
    for i, (op, a, b) in enumerate(gates):
        nodes[('w', i)] = (op, a, b)
    def ref_old(x):
        if x < N:
            return ('in', x)
        if x in Ws:
            o = outs.index(x)
            w = outsel[o]
            if w < len(ins):
                return ref_old(ins[w])
            return ('w', w - len(ins))
        return ('o', x)
    def ref_win(x):
        if x < len(ins):
            return ref_old(ins[x])
        return ('w', x - len(ins))
    deps = {}
    for key, (op, a, b) in nodes.items():
        if key[0] == 'o':
            ra, rb = ref_old(a), ref_old(b)
        else:
            ra, rb = ref_win(a), ref_win(b)
        deps[key] = (op, ra, rb)
    outkey = ref_old(N + s - 1)
    order = []
    state = {}
    def visit(key):
        if key[0] == 'in':
            return
        st = state.get(key)
        if st == 2:
            return
        if st == 1:
            raise ValueError('cycle')
        state[key] = 1
        op, ra, rb = deps[key]
        visit(ra)
        if op != 'not':
            visit(rb)
        state[key] = 2
        order.append(key)
    visit(outkey)
    idx = {}
    out = []
    def wid(r):
        if r[0] == 'in':
            return r[1]
        return idx[r]
    for key in order:
        op, ra, rb = deps[key]
        out.append((op, wid(ra), wid(rb) if op != 'not' else wid(ra)))
        idx[key] = N + len(out) - 1
    if outkey[0] == 'in':
        return None
    if order[-1] != outkey:
        return None
    return out

def random_windows(circ, k, count, rng):
    s = len(circ)
    nbr = {g: set() for g in range(N, N + s)}
    for i, (op, a, b) in enumerate(circ):
        g = N + i
        for x in ([a] if op == 'not' else [a, b]):
            if x >= N:
                nbr[g].add(x); nbr[x].add(g)
    seen = set()
    for _ in range(count):
        start = rng.randrange(N, N + s)
        W = {start}
        frontier = set(nbr[start])
        while len(W) < k and frontier:
            x = rng.choice(sorted(frontier))
            W.add(x)
            frontier |= nbr[x]
            frontier -= W
        if len(W) == k:
            fz = frozenset(W)
            if fz not in seen:
                seen.add(fz)
                yield fz

def improve(circ, ks, tries, rng, log):
    for k in ks:
        for W in random_windows(circ, k, tries, rng):
            r = try_window(circ, W)
            if r is None:
                continue
            ins, outs, gates, outsel = r
            new = splice(circ, W, ins, outs, gates, outsel)
            if new is None:
                continue
            new = clean(new)
            if ok(new) and len(new) < len(circ):
                return new
    return None

if __name__ == '__main__':
    path = sys.argv[1]
    ks = [int(x) for x in sys.argv[2].split(',')]
    tries = int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = random.Random(seed)
    circs = parse_sa(path)
    print('circuits', len(circs), flush=True)
    t0 = time.time()
    for ci, c in enumerate(circs):
        c = clean(c)
        assert ok(c), 'bad circuit'
        best = c
        while True:
            r = improve(best, ks, tries, rng, print)
            if r is None:
                break
            print('IMPROVED', len(best), '->', len(r), flush=True)
            best = r
        print(ci, 'size', len(c), '->', len(best), 'time', round(time.time() - t0), flush=True)
        if len(best) <= 19:
            print('FOUND19', best, flush=True)
