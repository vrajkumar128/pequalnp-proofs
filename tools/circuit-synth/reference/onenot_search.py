#!/usr/bin/env python3
"""L-meta-1444: exact SAT synthesis of minimum fan-in-2 AND/OR circuits (no NOT) and
AND/OR/NOT circuits with at most one NOT gate, for monotone functions of 5 inputs.

Usage:
  python3 onenot_search.py validate          # brute force vs SAT on all functions of 2 and 3 inputs
  python3 onenot_search.py run [T ...]       # the 10 shard functions (or the given hex tables)

Truth table convention: value at x (x_i in {0,1}) is bit sum_i x_i 2^i of T.

Normal form searched at size s (sound for a minimum circuit, see notes in main()):
  gates 0..s-1 are wires n..n+s-1; gate i reads a key (j,k), j<=k<n+i;
  j<k: AND or OR of wires j,k;  j=k: NOT of wire j (only when maxnot=1; at most one such gate);
  output = last gate; every other gate is read by a later gate;
  consecutive gates i,i+1 with gate i+1 not reading gate i have key(i) <= key(i+1);
  all wires (inputs and gates) compute pairwise distinct functions.
min size = first s (searched upward from 1) whose formula is SAT. Every SAT model is decoded,
written as a Lean-style gate list and evaluated with the exact Lean semantics on all rows.
"""
import itertools, os, subprocess, sys, time, tempfile

KISSAT = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1343/src/kissat/build/kissat'
CADICAL = '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1343/src/cadical/build/cadical'
HERE = os.path.dirname(os.path.abspath(__file__))
SHARD = [0xfeeafcc0, 0xeeeaeaea, 0xeeeaeee8, 0xeeeeeee0, 0xfee8eee8,
         0xfeeaeaaa, 0xfeeaeae8, 0xfeeaece8, 0xfeeaeee0, 0xfeeafcc8]


class CNF:
    def __init__(self):
        self.nv = 0
        self.cl = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, c):
        self.cl.append(c)


def encode(n, T, s, maxnot, symbreak=True):
    R = 1 << n
    f = CNF()
    keys = []      # keys[i] = list of (j,k)
    sel = []       # sel[i][(j,k)] = var
    op = []        # op[i]: true = OR, false = AND
    val = {}       # val[(w,t)] for gate wires
    for i in range(s):
        w = n + i
        ks = [(j, k) for j in range(w) for k in range(j + 1, w)]
        if maxnot:
            ks += [(j, j) for j in range(w)]
        keys.append(ks)
        sel.append({p: f.var() for p in ks})
        op.append(f.var())
        for t in range(R):
            val[(w, t)] = f.var()

    def lit(w, t):
        # returns ('c', bool) for constant input bit, or ('v', var)
        if w < n:
            return ('c', bool((t >> w) & 1))
        return ('v', val[(w, t)])

    def add_simpl(clause):
        # clause: list of ('c',bool) / ('v',+-var) literals; drop false consts, skip if true const
        out = []
        for l in clause:
            if l[0] == 'c':
                if l[1]:
                    return
            else:
                out.append(l[1])
        f.add(out)

    def neg(l):
        return ('c', not l[1]) if l[0] == 'c' else ('v', -l[1])

    for i in range(s):
        w = n + i
        sv = sel[i]
        ks = keys[i]
        # exactly one key
        f.add([sv[p] for p in ks])
        for a, b in itertools.combinations(ks, 2):
            f.add([-sv[a], -sv[b]])
        for p in ks:
            j, k = p
            S = ('v', -sv[p])
            for t in range(R):
                g = ('v', val[(w, t)])
                a = lit(j, t)
                if j == k:
                    # g = not a
                    add_simpl([S, g, a])
                    add_simpl([S, neg(g), neg(a)])
                    continue
                b = lit(k, t)
                OP = ('v', -op[i])   # literal "not OR" i.e. AND branch condition is op false
                ORl = ('v', op[i])
                # AND branch (op false): clauses get literal op (true when OR, satisfying them)
                add_simpl([S, ORl, neg(g), a])
                add_simpl([S, ORl, neg(g), b])
                add_simpl([S, ORl, g, neg(a), neg(b)])
                # OR branch (op true)
                add_simpl([S, OP, g, neg(a)])
                add_simpl([S, OP, g, neg(b)])
                add_simpl([S, OP, neg(g), a, b])
    # at most one NOT gate
    if maxnot:
        isnot = []
        for i in range(s):
            v = f.var()
            isnot.append(v)
            ns = [sel[i][(j, j)] for j in range(n + i)]
            for x in ns:
                f.add([-x, v])
            f.add([-v] + ns)
        for a, b in itertools.combinations(isnot, 2):
            f.add([-a, -b])
    # output = last gate
    wo = n + s - 1
    for t in range(R):
        f.add([val[(wo, t)] if (T >> t) & 1 else -val[(wo, t)]])
    if symbreak:
        # every non-output gate is read by a later gate
        for i in range(s - 1):
            w = n + i
            f.add([sel[i2][p] for i2 in range(i + 1, s) for p in keys[i2] if w in p])
        # canonical order of consecutive independent gates
        for i in range(s - 1):
            w = n + i
            for q in keys[i + 1]:
                if w in q:
                    continue
                for p in keys[i]:
                    if q < p:
                        f.add([-sel[i][p], -sel[i + 1][q]])
        # all wires compute distinct functions
        wires = list(range(n + s))
        for w1, w2 in itertools.combinations(wires, 2):
            if w2 < n:
                continue
            # exists t with val differs
            ds = []
            for t in range(R):
                if w1 < n:
                    b1 = (t >> w1) & 1
                    ds.append(-val[(w2, t)] if b1 else val[(w2, t)])
                else:
                    d = f.var()
                    ds.append(d)
                    x, y = val[(w1, t)], val[(w2, t)]
                    f.add([-d, x, y])
                    f.add([-d, -x, -y])
            f.add(ds)
    return f, keys, sel, op


def solve(f, timeout=3600, solver='kissat'):
    fd, path = tempfile.mkstemp(suffix='.cnf', dir=os.path.join(HERE, 'tmp'))
    with os.fdopen(fd, 'w') as h:
        h.write('p cnf %d %d\n' % (f.nv, len(f.cl)))
        for c in f.cl:
            h.write(' '.join(map(str, c)) + ' 0\n')
    t0 = time.time()
    try:
        cmd = [KISSAT, '-q', path] if solver == 'kissat' else [CADICAL, '-q', path]
        r = subprocess.run(['timeout', str(timeout)] + cmd,
                           capture_output=True, text=True)
    finally:
        os.unlink(path)
    dt = time.time() - t0
    model = set()
    status = None
    for line in r.stdout.splitlines():
        if line.startswith('s '):
            status = line[2:].strip()
        elif line.startswith('v '):
            for x in line[2:].split():
                x = int(x)
                if x > 0:
                    model.add(x)
    if status == 'SATISFIABLE':
        return True, model, dt
    if status == 'UNSATISFIABLE':
        return False, None, dt
    return None, None, dt


def decode(n, s, keys, sel, op, model):
    """Return a Lean-style gate list: (opname, [inputs])."""
    gates = []
    for i in range(s):
        p = [p for p in keys[i] if sel[i][p] in model]
        assert len(p) == 1
        j, k = p[0]
        if j == k:
            gates.append(('not', [j]))
        else:
            gates.append(('or' if op[i] in model else 'and', [j, k]))
    return gates, n + s - 1


def lean_eval(gates, o, x):
    """Exact copy of PEqualNP.CircuitLowerBounds.Circuit.eval semantics."""
    w = list(x)
    for (opn, ins) in gates:
        vs = [w[i] if i < len(w) else False for i in ins]
        if opn == 'and':
            r = all(vs)
        elif opn == 'or':
            r = any(vs)
        elif opn == 'not':
            r = not (vs[0] if vs else False)
        else:
            raise ValueError(opn)
        w.append(r)
    return w[o] if o < len(w) else False


def check_circuit(n, T, gates, o, maxnot):
    assert all(len(ins) <= 2 for _, ins in gates)
    assert sum(1 for g in gates if g[0] == 'not') <= maxnot
    for t in range(1 << n):
        x = [bool((t >> i) & 1) for i in range(n)]
        if lean_eval(gates, o, x) != bool((T >> t) & 1):
            return False
    return True


def min_size(n, T, maxnot, smax, log=None, timeout=3600, symbreak=True):
    """Search s = 1..smax. Returns (min s or None, circuit, per-size records)."""
    recs = []
    for s in range(1, smax + 1):
        f, keys, sel, op = encode(n, T, s, maxnot, symbreak)
        res, model, dt = solve(f, timeout)
        recs.append((s, res, round(dt, 3), f.nv, len(f.cl)))
        if log:
            log('  T=%#x maxnot=%d s=%d -> %s  %.2fs  (%d vars, %d clauses)' %
                (T, maxnot, s, {True: 'SAT', False: 'UNSAT', None: 'TIMEOUT'}[res], dt, f.nv, len(f.cl)))
        if res is None:
            return None, None, recs
        if res:
            gates, o = decode(n, s, keys, sel, op, model)
            assert check_circuit(n, T, gates, o, maxnot), 'decoded circuit wrong'
            return s, (gates, o), recs
    return None, None, recs


# ---------------- brute force (for validation) ----------------
def brute_min_sizes(n, maxlevel):
    """BFS over sets of wire functions. Returns dict (func, maxnot) -> min gates (<= maxlevel)."""
    R = 1 << n
    M = (1 << R) - 1
    inputs = []
    for i in range(n):
        inputs.append(sum(1 << t for t in range(R) if (t >> i) & 1))
    best = {}
    for x in inputs:
        best[(x, 0)] = 0
        best[(x, 1)] = 0
    level = {(frozenset(inputs), 0)}
    for L in range(1, maxlevel + 1):
        nxt = set()
        for (S, used) in level:
            lst = list(S)
            cand = set()
            for a, b in itertools.combinations(lst, 2):
                cand.add((a & b, used))
                cand.add((a | b, used))
            if not used:
                for a in lst:
                    cand.add(((~a) & M, 1))
            for (g, u) in cand:
                if g in S:
                    continue
                nxt.add((S | {g}, u))
                for mn in ((1,) if u else (0, 1)):
                    if (g, mn) not in best:
                        best[(g, mn)] = L
        level = nxt
        print('  brute n=%d level %d: %d states' % (n, L, len(level)), flush=True)
    return best


def validate():
    log = lambda m: print(m, flush=True)
    t0 = time.time()
    ok = True
    # spot checks
    maj3 = sum(1 << t for t in range(8) if bin(t).count('1') >= 2)
    s, c, _ = min_size(3, maj3, 0, 6)
    log('maj3 NOT-free min = %s (expect 4) %s' % (s, c))
    ok &= (s == 4)
    s1, c1, _ = min_size(3, maj3, 1, 6)
    log('maj3 one-NOT min = %s (expect 4)' % s1)
    ok &= (s1 == 4)
    xor2 = 0b0110
    s, c, _ = min_size(2, xor2, 1, 6)
    log('xor2 one-NOT min = %s (expect 4) %s' % (s, c))
    ok &= (s == 4)
    for n, maxlevel in ((2, 6), (3, 6)):
        best = brute_min_sizes(n, maxlevel)
        R = 1 << n
        cnt = 0
        for T in range(1 << R):
            mono = all(((T >> x) & 1) <= ((T >> (x | (1 << i))) & 1) for x in range(R) for i in range(n))
            for maxnot in (0, 1):
                if maxnot == 0 and not mono:
                    continue
                bb = best.get((T, maxnot))
                proj = any(T == sum(1 << t for t in range(R) if (t >> i) & 1) for i in range(n))
                if proj:
                    continue   # size 0 functions are outside the SAT normal form (output = gate)
                s, c, _ = min_size(n, T, maxnot, maxlevel)
                # plain encoding without symmetry breaking as a second check
                s2, c2, _ = min_size(n, T, maxnot, maxlevel, symbreak=False)
                good = (s == bb == s2)
                cnt += 1
                if not good:
                    ok = False
                    log('MISMATCH n=%d T=%#x maxnot=%d brute=%s sat=%s sat_nosb=%s' % (n, T, maxnot, bb, s, s2))
        log('n=%d: %d (function, maxnot) cases compared up to %d gates' % (n, cnt, maxlevel))
    log('validate: all ok = %s, %.1fs' % (ok, time.time() - t0))
    return ok


def run(Ts):
    log = lambda m: print(m, flush=True)
    table = []
    for T in Ts:
        R = 32
        mono = all(((T >> x) & 1) <= ((T >> (x | (1 << i))) & 1) for x in range(R) for i in range(5))
        assert mono, hex(T)
        t0 = time.time()
        a, ca, ra = min_size(5, T, 0, 20, log)
        ta = time.time() - t0
        t0 = time.time()
        b, cb, rb = min_size(5, T, 1, a, log)
        tb = time.time() - t0
        log('RESULT T=%#x (a)=%s (b)=%s  time a %.1fs b %.1fs' % (T, a, b, ta, tb))
        log('  NOT-free circuit: %s' % (ca,))
        log('  one-NOT  circuit: %s' % (cb,))
        table.append((T, a, b, ta, tb))
    log('\nTABLE  T  (a) NOT-free min  (b) <=1 NOT min  saving?')
    for T, a, b, ta, tb in table:
        log('%#010x  %s  %s  %s  (%.1fs, %.1fs)' % (T, a, b, 'YES' if b < a else 'no', ta, tb))


def validate4(maxlevel=5, nrandom=150):
    """n=4: brute force (levels <= maxlevel) vs SAT on all monotone functions (both modes)
    and on random non-monotone functions (one-NOT mode)."""
    import random
    log = lambda m: print(m, flush=True)
    t0 = time.time()
    best = brute_min_sizes(4, maxlevel)
    R = 16
    projs = {sum(1 << t for t in range(R) if (t >> i) & 1) for i in range(4)}
    monos = [T for T in range(1 << R)
             if all(((T >> x) & 1) <= ((T >> (x | (1 << i))) & 1) for x in range(R) for i in range(4))]
    rng = random.Random(1444)
    others = [T for T in rng.sample(range(1 << R), 4 * nrandom) if T not in monos][:nrandom]
    # include functions that brute force reaches with one NOT, to have SAT-positive cases
    reach = sorted(T for (T, m) in best if m == 1 and T not in monos and T not in projs)
    others += rng.sample(reach, min(nrandom, len(reach)))
    ok = True
    cnt = 0
    for T, modes in [(T, (0, 1)) for T in monos] + [(T, (1,)) for T in others]:
        if T in projs or T in (0, (1 << R) - 1):
            continue
        for maxnot in modes:
            bb = best.get((T, maxnot))
            s, c, _ = min_size(4, T, maxnot, maxlevel)
            cnt += 1
            if s != bb:
                ok = False
                log('MISMATCH n=4 T=%#x maxnot=%d brute=%s sat=%s' % (T, maxnot, bb, s))
    log('n=4: %d cases compared up to %d gates; validate4 all ok = %s, %.1fs' %
        (cnt, maxlevel, ok, time.time() - t0))


def crosscheck(pairs):
    """pairs: list of (T, a). Independent re-check that no circuit with <= 1 NOT and
    at most a-1 gates exists: (1) plain encoding (no symmetry breaking) with kissat for
    every s = 1..a-1, (2) symmetry-broken encoding with CaDiCaL at s = a-1."""
    log = lambda m: print(m, flush=True)
    ok = True
    for T, a in pairs:
        t0 = time.time()
        for s in range(1, a):
            f, *_ = encode(5, T, s, 1, symbreak=False)
            res, _, dt = solve(f, 3600, 'kissat')
            log('  plain  T=%#x maxnot=1 s=%d -> %s %.2fs' % (T, s, res, dt))
            ok &= (res is False)
        f, *_ = encode(5, T, a - 1, 1, symbreak=True)
        res, _, dt = solve(f, 3600, 'cadical')
        log('  cadical T=%#x maxnot=1 s=%d -> %s %.2fs' % (T, a - 1, res, dt))
        ok &= (res is False)
        log('CROSS T=%#x a=%d done %.1fs ok=%s' % (T, a, time.time() - t0, ok))
    log('crosscheck: all ok = %s' % ok)


if __name__ == '__main__':
    os.makedirs(os.path.join(HERE, 'tmp'), exist_ok=True)
    if sys.argv[1] == 'validate':
        validate()
    elif sys.argv[1] == 'validate4':
        validate4()
    elif sys.argv[1] == 'crosscheck':
        crosscheck([(int(x.split(':')[0], 16), int(x.split(':')[1])) for x in sys.argv[2:]])
    elif sys.argv[1] == 'run':
        Ts = [int(x, 16) for x in sys.argv[2:]] or SHARD
        run(Ts)
