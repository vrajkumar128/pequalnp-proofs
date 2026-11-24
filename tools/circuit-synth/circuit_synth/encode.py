"""CNF encodings of "a circuit with exactly s gates computes the outputs on the given rows".

Two encodings (see README for the soundness arguments):

* NF  (normal form, default): gate j is AND/OR of two distinct earlier wires a < b, or NOT of
  one earlier wire (when the basis allows NOT). Optional symmetry breaking (all sound, each one
  separately switchable and cross-checked):
    used      every gate is read by a later gate or is an output
    distinct  every gate's row vector differs from every earlier wire and from both constants
    order     greedy topological order: key (b, a, kind) strictly increasing over the free gates
              (kind: OR < AND; a NOT gate has a = b)
    relevant  every input the outputs depend on is read by some gate
  A size-s NF instance is UNSAT  =>  no circuit of any shape with exactly s gates; to exclude
  "<= s" the driver proves every size 1..s (minimum search goes upwards).

* RAW: every Lean FanInTwo gate, degenerate ones included (0, 1 or 2 inputs, inputs that do not
  exist yet, NOT with an ignored second input): gate j = op(src1, src2) with src in
  wires(0..n+j-1) + {TRUE (= input omitted from an AND), FALSE (= missing wire / omitted from an
  OR or NOT)}; outputs may be any wire or a missing one. No symmetry breaking at all. Because
  AND [] gates can be appended without changing anything, RAW at size s covers every circuit
  with at most s gates (when no gate-property side constraint is used).

Side constraints (both encodings): fixed first gates (NF), "some gate with op OP is true on
row r" (exists), "no gate with op OP is true on row r" (forbid), and gate-elimination bounds "under the restriction x_P = 1, x_Q = 0 at most s - L
gates have an input that is constant" (L a lower bound for the restricted function).
"""
from .core import lean_wires


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def var(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        out = []
        for l in cl:
            if l is True:
                return
            if l is False:
                continue
            out.append(l)
        self.clauses.append(out)

    def dimacs(self, comments=()):
        lines = ['c ' + c for c in comments]
        lines.append('p cnf %d %d' % (self.nv, len(self.clauses)))
        lines.extend(' '.join(map(str, c)) + ' 0' for c in self.clauses)
        return '\n'.join(lines) + '\n'


def neg(l):
    if l is True:
        return False
    if l is False:
        return True
    return -l


def ladder(cnf, X):
    """Exactly one of X, with order variables: returns ul, ul(i) <=> (selected index >= i)."""
    m = len(X)
    U = [None] + [cnf.var() for _ in range(1, m)]

    def ul(i):
        if i <= 0:
            return True
        if i >= m:
            return False
        return U[i]
    for i in range(m):
        cnf.add([neg(ul(i)), ul(i + 1), X[i]])
        cnf.add([-X[i], ul(i)])
        cnf.add([-X[i], neg(ul(i + 1))])
        if i >= 1:
            cnf.add([neg(ul(i + 1)), ul(i)])
    return ul


def atmost(cnf, xs, k):
    """Sinz sequential counter: at most k of the literals xs are true."""
    xs = [x for x in xs if x is not False]
    k -= sum(1 for x in xs if x is True)
    xs = [x for x in xs if x is not True]
    m = len(xs)
    if k < 0:
        cnf.add([])
        return
    if k >= m:
        return
    if k == 0:
        for x in xs:
            cnf.add([-x])
        return
    r = [[cnf.var() for _ in range(k)] for _ in range(m)]
    for i in range(m):
        x = xs[i]
        cnf.add([-x, r[i][0]])
        if i > 0:
            for c in range(k):
                cnf.add([-r[i - 1][c], r[i][c]])
            for c in range(1, k):
                cnf.add([-x, -r[i - 1][c - 1], r[i][c]])
            cnf.add([-x, -r[i - 1][k - 1]])


class SB:
    FLAGS = ('used', 'distinct', 'order', 'relevant')

    def __init__(self, used=True, distinct=True, order=True, relevant=True):
        self.used, self.distinct, self.order, self.relevant = used, distinct, order, relevant

    @staticmethod
    def parse(s):
        s = (s or 'all').strip()
        if s == 'all':
            return SB()
        if s == 'none':
            return SB(False, False, False, False)
        names = [x for x in s.split(',') if x]
        bad = set(names) - set(SB.FLAGS)
        if bad:
            raise ValueError('unknown symmetry-breaking flags %s' % sorted(bad))
        return SB(*[f in names for f in SB.FLAGS])

    def name(self):
        on = [f for f in self.FLAGS if getattr(self, f)]
        return ','.join(on) if on else 'none'


def subcube(n, P, Q):
    pm = sum(1 << i for i in P)
    qm = sum(1 << i for i in Q)
    return [t for t in range(1 << n) if (t & pm) == pm and not (t & qm)]


class Instance:
    """One encoded instance. `decode(model)` returns a core.Circuit (before trivial outputs are
    re-attached by the driver)."""

    def __init__(self, cnf, meta):
        self.cnf, self.meta = cnf, meta


def needed_rows(n, rows, basis, exists, restrictions):
    rs = set(rows)
    for op, t in exists:
        rs.add(t)
    for P, Q, L in restrictions:
        if basis.max_not == 0:
            rs.add(sum(1 << i for i in P))
            rs.add(((1 << n) - 1) & ~sum(1 << i for i in Q))
        else:
            rs.update(subcube(n, P, Q))
    return sorted(rs)


def _elim_clauses(cnf, n, rows, basis, P, Q, valsel, e):
    """valsel: per-row literals of one selected input of a gate. Force e when that input is
    constant under the restriction x_P = 1, x_Q = 0 (monotone: two rows decide it)."""
    ridx = {t: r for r, t in enumerate(rows)}
    if basis.max_not == 0:
        tP = ridx[sum(1 << i for i in P)]
        tV = ridx[((1 << n) - 1) & ~sum(1 << i for i in Q)]
        cnf.add([neg(valsel[tP]), e])          # 1 on the least point => constant 1
        cnf.add([valsel[tV], e])               # 0 on the greatest point => constant 0
    else:
        sub = [ridx[t] for t in subcube(n, P, Q)]
        cnf.add([e] + [neg(valsel[r]) for r in sub])
        cnf.add([e] + [valsel[r] for r in sub])


def prefix_eliminable(n, prefix, j, P, Q):
    """Is fixed gate j removable under the restriction (constant input, missing input,
    fewer than two distinct inputs, or constant itself)?"""
    op, ins = prefix[j]
    sub = subcube(n, P, Q)
    W = [lean_wires(prefix[:j + 1], [bool((t >> i) & 1) for i in range(n)]) for t in sub]
    if len(set(w[n + j] for w in W)) <= 1:
        return True
    if op == 'not':
        ins = ins[:1]
    if op != 'not' and len(set(ins)) < 2:
        return True
    for i in ins:
        if i >= n + j or len(set(w[i] for w in W)) <= 1:
            return True
    return False


def encode_nf(n, rows, outs, basis, s, prefix=(), sb=None, exists=(), restrictions=(),
              depend=None, forbid=()):
    """outs: truth tables (ints over all 2^n inputs) of the outputs that must be computed by a
    gate (non-constant, non-projection; duplicates removed). rows: input indices to constrain.
    prefix: fixed first gates (op, inputs) in Lean form. depend: inputs some output depends on.
    """
    sb = sb or SB()
    prefix = [(op, list(ins)) for op, ins in prefix]
    m = len(prefix)
    assert s >= m
    rows = needed_rows(n, rows, basis, list(exists) + list(forbid), restrictions)
    R = len(rows)
    cnf = CNF()
    rowx = [[bool((t >> i) & 1) for i in range(n)] for t in rows]
    pw = [lean_wires(prefix, rowx[r]) for r in range(R)]
    nfix = n + m

    def fixed(w, r):
        return pw[r][w]

    allow_not = basis.allow_not
    single_last = (len(outs) == 1 and m == 0)
    free = list(range(m, s))
    A, B, ulA, ulB, op, isnot, v, va, vb = {}, {}, {}, {}, {}, {}, {}, {}, {}

    def val(w, r):
        if w < nfix:
            return fixed(w, r)
        return v[w - n][r]

    for j in free:
        W = n + j
        A[j] = [cnf.var() for _ in range(W)]
        B[j] = [cnf.var() for _ in range(W)]
        ulA[j] = ladder(cnf, A[j])
        ulB[j] = ladder(cnf, B[j])
        op[j] = cnf.var()                       # true = AND, false = OR
        isnot[j] = cnf.var() if allow_not else False
        for w in range(W):
            cnf.add([-A[j][w], ulB[j](w if allow_not else w + 1)])    # a <= b (a < b if no NOT)
            if allow_not:
                cnf.add([-A[j][w], -B[j][w], isnot[j]])
                cnf.add([-isnot[j], -A[j][w], B[j][w]])
        if allow_not:
            cnf.add([-isnot[j], -op[j]])
        v[j] = [cnf.var() for _ in range(R)]
        va[j] = [cnf.var() for _ in range(R)]
        vb[j] = [cnf.var() for _ in range(R)]
        for r in range(R):
            for w in range(W):
                x = val(w, r)
                for X, y in ((A[j][w], va[j][r]), (B[j][w], vb[j][r])):
                    cnf.add([-X, neg(x), y])
                    cnf.add([-X, x, -y])
            g, xa, xb, o, t = v[j][r], va[j][r], vb[j][r], op[j], isnot[j]
            cnf.add([neg(t), g, xa])
            cnf.add([neg(t), -g, -xa])
            cnf.add([t, -o, -g, xa])
            cnf.add([t, -o, -g, xb])
            cnf.add([t, -o, g, -xa, -xb])
            cnf.add([t, o, g, -xa])
            cnf.add([t, o, g, -xb])
            cnf.add([t, o, -g, xa, xb])

    # NOT budget
    if basis.max_not is not None:
        pn = sum(1 for o_, _ in prefix if o_ == 'not')
        atmost(cnf, [isnot[j] for j in free], basis.max_not - pn)
    elif any(o_ == 'not' for o_, _ in prefix) and not allow_not:
        cnf.add([])

    # outputs
    outsel = []
    if single_last:
        if s == 0:
            cnf.add([])
        else:
            for r, t in enumerate(rows):
                cnf.add([v[s - 1][r] if (outs[0] >> t) & 1 else -v[s - 1][r]])
    else:
        for tt in outs:
            sel = {}
            for w in range(n, nfix):
                if all(fixed(w, r) == bool((tt >> t) & 1) for r, t in enumerate(rows)):
                    sel[w] = cnf.var()
            for j in free:
                x = cnf.var()
                sel[n + j] = x
                for r, t in enumerate(rows):
                    cnf.add([-x, v[j][r] if (tt >> t) & 1 else -v[j][r]])
            cnf.add(list(sel.values()))
            outsel.append(sel)

    # symmetry breaking
    if sb.used:
        for j in free:
            if single_last and j == s - 1:
                continue
            w = n + j
            lits = [X[k][w] for k in free if k > j for X in (A, B)]
            lits += [sel[w] for sel in outsel if w in sel]
            cnf.add(lits)
    if sb.distinct:
        for j in free:
            cnf.add([v[j][r] for r in range(R)])
            cnf.add([-v[j][r] for r in range(R)])
            for w in range(nfix):
                cnf.add([(-v[j][r] if fixed(w, r) else v[j][r]) for r in range(R)])
            for k in free:
                if k >= j:
                    break
                ds = []
                for r in range(R):
                    d = cnf.var()
                    cnf.add([-d, v[k][r], v[j][r]])
                    cnf.add([-d, -v[k][r], -v[j][r]])
                    ds.append(d)
                cnf.add(ds)
    if sb.order:
        # With one output fixed at the last gate and `used` off, unused gates may exist, so the
        # output gate need not be the unique sink: order only the gates before it (the greedy
        # argument then keeps the output last).
        ordered = [j for j in free if not (single_last and not sb.used and j == s - 1)]
        for p in ordered:
            for q in ordered:
                if q <= p:
                    continue
                eqb, eqab = cnf.var(), cnf.var()
                for beta in range(n + p):
                    cnf.add([-B[q][beta], neg(ulB[p](beta + 1))])     # b_p <= b_q
                    cnf.add([-B[q][beta], -B[p][beta], eqb])
                for alpha in range(n + p):
                    cnf.add([-eqb, -A[q][alpha], neg(ulA[p](alpha + 1))])   # a_p <= a_q
                    cnf.add([-eqb, -A[q][alpha], -A[p][alpha], eqab])
                cnf.add([-eqab, -op[p]])                                  # same inputs:
                cnf.add([-eqab, op[q]])                                   # OR before AND
    if sb.relevant and depend:
        read_by_prefix = set(i for o_, ins in prefix for i in (ins[:1] if o_ == 'not' else ins))
        for i in depend:
            if i not in read_by_prefix:
                cnf.add([X[j][i] for j in free for X in (A, B)])

    # side constraints
    ridx = {t: r for r, t in enumerate(rows)}
    for (gop, t) in exists:
        r = ridx[t]
        if any(prefix[j][0] == gop and pw[r][n + j] for j in range(m)):
            continue
        ds = []
        for j in free:
            d = cnf.var()
            cnf.add([-d, v[j][r]])
            if gop == 'not':
                cnf.add([-d, isnot[j]])
            else:
                cnf.add([-d, neg(isnot[j])])
                cnf.add([-d, op[j] if gop == 'and' else -op[j]])
            ds.append(d)
        cnf.add(ds)
    for (gop, t) in forbid:
        r = ridx[t]
        if any(prefix[j][0] == gop and pw[r][n + j] for j in range(m)):
            cnf.add([])
        for j in free:
            if gop == 'not':
                cnf.add([neg(isnot[j]), -v[j][r]])
            else:
                cnf.add([isnot[j], -op[j] if gop == 'and' else op[j], -v[j][r]])
    for (P, Q, L) in restrictions:
        pe = sum(1 for j in range(m) if prefix_eliminable(n, prefix, j, P, Q))
        es = []
        for j in free:
            e = cnf.var()
            _elim_clauses(cnf, n, rows, basis, P, Q, va[j], e)
            _elim_clauses(cnf, n, rows, basis, P, Q, vb[j], e)
            es.append(e)
        atmost(cnf, es, s - L - pe)

    meta = dict(kind='nf', n=n, s=s, rows=rows, prefix=prefix, A=A, B=B, op=op, isnot=isnot,
                outsel=outsel, single_last=single_last, free=free)
    return Instance(cnf, meta)


def encode_raw(n, rows, outs, basis, s, exists=(), restrictions=(), forbid=()):
    """outs: truth tables of ALL outputs (constants and projections included)."""
    rows = needed_rows(n, rows, basis, list(exists) + list(forbid), restrictions)
    R = len(rows)
    cnf = CNF()
    rowx = [[bool((t >> i) & 1) for i in range(n)] for t in rows]
    ops = ['and', 'or'] + (['not'] if basis.allow_not else [])
    S1, S2, OP, v, s1, s2 = {}, {}, {}, {}, {}, {}

    def val(w, r):
        if w < n:
            return rowx[r][w]
        return v[w - n][r]

    for j in range(s):
        W = n + j
        TR, FA = W, W + 1                       # source indices for TRUE and FALSE
        S1[j] = [cnf.var() for _ in range(W + 2)]
        S2[j] = [cnf.var() for _ in range(W + 2)]
        ladder(cnf, S1[j])
        ladder(cnf, S2[j])
        OP[j] = {o: cnf.var() for o in ops}
        ladder(cnf, list(OP[j].values()))
        cnf.add([-OP[j]['or'], -S1[j][TR]])     # an OR gate has no TRUE input in Lean
        cnf.add([-OP[j]['or'], -S2[j][TR]])
        if 'not' in OP[j]:
            cnf.add([-OP[j]['not'], -S1[j][TR]])
        v[j] = [cnf.var() for _ in range(R)]
        s1[j] = [cnf.var() for _ in range(R)]
        s2[j] = [cnf.var() for _ in range(R)]
        for r in range(R):
            for w in range(W + 2):
                x = val(w, r) if w < W else (w == TR)
                for X, y in ((S1[j][w], s1[j][r]), (S2[j][w], s2[j][r])):
                    cnf.add([-X, neg(x), y])
                    cnf.add([-X, x, -y])
            g, a, b = v[j][r], s1[j][r], s2[j][r]
            o = OP[j]['and']
            cnf.add([-o, -g, a])
            cnf.add([-o, -g, b])
            cnf.add([-o, g, -a, -b])
            o = OP[j]['or']
            cnf.add([-o, g, -a])
            cnf.add([-o, g, -b])
            cnf.add([-o, -g, a, b])
            if 'not' in OP[j]:
                o = OP[j]['not']
                cnf.add([-o, g, a])
                cnf.add([-o, -g, -a])
    if basis.max_not is not None and basis.max_not > 0:
        atmost(cnf, [OP[j]['not'] for j in range(s)], basis.max_not)
    outsel = []
    for tt in outs:
        sel = [cnf.var() for _ in range(n + s + 1)]   # wire n+s = missing wire (false)
        ladder(cnf, sel)
        for w in range(n + s + 1):
            for r, t in enumerate(rows):
                want = bool((tt >> t) & 1)
                x = val(w, r) if w < n + s else False
                cnf.add([-sel[w], x if want else neg(x)])
        outsel.append(sel)
    ridx = {t: r for r, t in enumerate(rows)}
    for (gop, t) in exists:
        r = ridx[t]
        ds = []
        for j in range(s):
            d = cnf.var()
            cnf.add([-d, v[j][r]])
            cnf.add([-d, OP[j][gop]] if gop in OP[j] else [-d])
            ds.append(d)
        cnf.add(ds)
    for (gop, t) in forbid:
        r = ridx[t]
        for j in range(s):
            if gop in OP[j]:
                cnf.add([-OP[j][gop], -v[j][r]])
    for (P, Q, L) in restrictions:
        es = []
        for j in range(s):
            e = cnf.var()
            _elim_clauses(cnf, n, rows, basis, P, Q, s1[j], e)
            # the second source matters only for AND/OR
            e2 = cnf.var()
            _elim_clauses(cnf, n, rows, basis, P, Q, s2[j], e2)
            if 'not' in OP[j]:
                cnf.add([-e2, OP[j]['not'], e])
            else:
                cnf.add([-e2, e])
            es.append(e)
        atmost(cnf, es, s - L)
    meta = dict(kind='raw', n=n, s=s, rows=rows, S1=S1, S2=S2, OP=OP, outsel=outsel)
    return Instance(cnf, meta)


def _one(xs, model):
    hits = [i for i, x in enumerate(xs) if x in model]
    assert len(hits) == 1, hits
    return hits[0]


def decode(inst, model):
    """model: set of true variables. Returns (gates, outputs) in Lean form."""
    m = inst.meta
    n, s = m['n'], m['s']
    if m['kind'] == 'nf':
        gates = [tuple(g) for g in m['prefix']]
        for j in m['free']:
            a = _one(m['A'][j], model)
            b = _one(m['B'][j], model)
            if a == b:
                gates.append(('not', [a]))
            else:
                gates.append(('and' if m['op'][j] in model else 'or', [a, b]))
        if m['single_last']:
            outs = [n + s - 1]
        else:
            outs = [min(w for w, x in sel.items() if x in model) for sel in m['outsel']]
        return gates, outs
    gates = []
    for j in range(s):
        W = n + j
        TR, FA = W, W + 1
        o = [k for k, x in m['OP'][j].items() if x in model]
        assert len(o) == 1
        o = o[0]
        a = _one(m['S1'][j], model)
        b = _one(m['S2'][j], model)
        if o == 'and':
            ins = [(W if x == FA else x) for x in (a, b) if x != TR]   # own index: missing wire
        elif o == 'or':
            ins = [x for x in (a, b) if x != FA]
        else:
            ins = [] if a == FA else [a]
        gates.append((o, ins))
    outs = [_one(sel, model) for sel in m['outsel']]
    return gates, outs
