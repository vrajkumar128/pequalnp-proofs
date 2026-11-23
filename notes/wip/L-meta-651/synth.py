import sys, time, itertools, random, argparse
from pysat.solvers import Solver

N = 10
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
ADJ = set()
for a,b in EDGES:
    ADJ.add((a,b)); ADJ.add((b,a))

def f_of(t):
    for a,b in EDGES:
        if (t>>a)&1 and (t>>b)&1:
            return 1
    return 0

FT = [f_of(t) for t in range(1<<N)]

def set_graph(n, edges):
    global N, EDGES, ADJ, FT
    N = n; EDGES = list(edges)
    ADJ = set()
    for a,b in EDGES:
        ADJ.add((a,b)); ADJ.add((b,a))
    FT = [f_of(t) for t in range(1<<N)]

def critical_rows():
    rows = []
    for a,b in EDGES:
        rows.append((1<<a)|(1<<b))
    for t in range(1<<N):
        if FT[t]==0:
            maximal = all(FT[t|(1<<v)]==1 for v in range(N) if not (t>>v)&1)
            if maximal:
                rows.append(t)
    return rows

class Enc:
    def __init__(self, s, shard=None, monotone=False, solver='cadical195', prune=True, nonot_input=False):
        self.s = s
        self.nv = 0
        self.cl = []
        self.monotone = monotone
        S = Solver(name=solver)
        self.S = S
        self.L = []; self.R = []; self.TA=[]; self.TO=[]; self.TN=[]
        for i in range(s):
            g = N+i
            self.L.append([self.new() for _ in range(g)])
            self.R.append([self.new() for _ in range(g)])
            self.TA.append(self.new()); self.TO.append(self.new()); self.TN.append(self.new())
        self.rows = []
        self.V = {}
        self.A = {}
        self.B = {}
        for i in range(s):
            g = N+i
            L, R = self.L[i], self.R[i]
            self.exactly_one(L); self.exactly_one(R)
            self.exactly_one([self.TA[i], self.TO[i], self.TN[i]])
            if monotone:
                self.add([-self.TN[i]])
            for j in range(g):
                for k in range(j):
                    self.add([-L[j], -R[k]])
                self.add([-self.TN[i], -L[j], R[j]])
                self.add([self.TN[i], -L[j], -R[j]])
            if i < s-1:
                self.add([self.R[i2][g] for i2 in range(i+1, s)] + [self.L[i2][g] for i2 in range(i+1, s)])
        for i in range(s-1):
            g = N+i
            u = self.R[i+1][g]
            E = self.new()
            for j in range(g):
                self.add([-self.L[i][j], -self.L[i+1][j], E])
                for j2 in range(j):
                    self.add([u, -self.L[i][j], -self.L[i+1][j2]])
            for k in range(g):
                for k2 in range(k):
                    self.add([u, -E, -self.R[i][k], -self.R[i+1][k2]])
            Q = self.new()
            for k in range(g):
                self.add([-E, -self.R[i][k], -self.R[i+1][k], Q])
            self.add([u, -Q, self.TA[i]])
            self.add([u, -Q, self.TO[i+1]])
        if prune:
            for m in range(s):
                gm = N+m
                for i in range(m+1, s):
                    self.add([-self.TN[i], -self.L[i][gm], -self.TN[m]])
                    for j in range(gm):
                        for X in (self.L[m][j], self.R[m][j]):
                            self.add([self.TN[m], -X, -self.L[i][j], -self.R[i][gm], self.TN[i]])
                        self.add([-self.TN[m], -self.L[m][j], -self.L[i][j], -self.R[i][gm], self.TN[i]])
        for v in range(N):
            self.add([self.L[i][v] for i in range(s)] + [self.R[i][v] for i in range(s)])
        for m in range(s):
            for i in range(m+1, s):
                EL = self.new(); ER = self.new()
                for j in range(N+m):
                    self.add([-self.L[m][j], -self.L[i][j], EL])
                    self.add([-self.R[m][j], -self.R[i][j], ER])
                for X, Y in ((self.TA[m], self.TA[i]), (self.TO[m], self.TO[i]), (self.TN[m], self.TN[i])):
                    self.add([-EL, -ER, -X, -Y])
        if nonot_input:
            for i in range(s):
                for j in range(N):
                    self.add([-self.TN[i], -self.L[i][j]])
        if shard is not None:
            self.apply_shard(shard)

    def apply_shard(self, shard):
        s = self.s
        if shard == 4:
            self.add([self.L[0][0]]); self.add([self.R[0][2]]); self.add([self.TA[0]])
            for i in range(1, s):
                for k in range(N):
                    self.add([-self.R[i][k], self.TA[i]])
                    for j in range(k):
                        if (j,k) in ADJ:
                            self.add([-self.L[i][j], -self.R[i][k]])
        elif shard == 0:
            self.add([self.L[0][0]]); self.add([self.R[0][1]]); self.add([self.TA[0]])
        elif shard == 1:
            self.add([self.L[0][0]]); self.add([self.R[0][1]]); self.add([self.TO[0]])
            for i in range(1, s):
                for k in range(N):
                    for j in range(k):
                        if (j,k) in ADJ:
                            self.add([-self.L[i][j], -self.R[i][k], -self.TA[i]])
        elif shard == 2:
            self.add([self.L[0][0]]); self.add([self.R[0][2]]); self.add([self.TO[0]])
            for i in range(1, s):
                for k in range(N):
                    for j in range(k):
                        if (j,k) in ADJ:
                            self.add([-self.L[i][j], -self.R[i][k], -self.TA[i]])
                            self.add([-self.L[i][j], -self.R[i][k], -self.TO[i]])
        elif shard == 3:
            self.add([self.L[0][0]]); self.add([self.TN[0]])
            for i in range(1, s):
                for k in range(N):
                    for j in range(k):
                        if (j,k) in ADJ:
                            self.add([-self.L[i][j], -self.R[i][k], -self.TA[i]])
                            self.add([-self.L[i][j], -self.R[i][k], -self.TO[i]])
                        else:
                            self.add([-self.L[i][j], -self.R[i][k], -self.TO[i]])

    def add_implied_mono(self, rows):
        s = self.s
        for t in rows:
            inr = [v for v in range(N) if (t>>v)&1]
            outr = [v for v in range(N) if not (t>>v)&1]
            lits = []
            for i in range(s):
                if FT[t]:
                    y = self.new(); z = self.new()
                    self.add([-y, self.TO[i]])
                    self.add([-y] + [self.L[i][v] for v in inr] + [self.R[i][v] for v in inr])
                    self.add([-z, self.TA[i]])
                    self.add([-z] + [self.L[i][v] for v in inr])
                    self.add([-z] + [self.R[i][v] for v in inr])
                else:
                    y = self.new(); z = self.new()
                    self.add([-y, self.TA[i]])
                    self.add([-y] + [self.L[i][v] for v in outr] + [self.R[i][v] for v in outr])
                    self.add([-z, self.TO[i]])
                    self.add([-z] + [self.L[i][v] for v in outr])
                    self.add([-z] + [self.R[i][v] for v in outr])
                lits += [y, z]
            self.add(lits)

    def add_demorgan_rule(self):
        s = self.s
        reads = {}
        for m in range(s):
            gm = N + m
            for i in range(m+1, s):
                r = self.new()
                self.add([-self.L[i][gm], r]); self.add([-self.R[i][gm], r])
                self.add([-r, self.L[i][gm], self.R[i][gm]])
                reads[(i, m)] = r
        other = {}
        for m in range(s):
            for i in range(m+1, s):
                o = self.new()
                self.add([-o] + [reads[(i2, m)] for i2 in range(m+1, s) if i2 != i])
                other[(m, i)] = o
        for i in range(s):
            for m1 in range(i):
                for m2 in range(m1+1, i):
                    self.add([self.TN[i], -self.L[i][N+m1], -self.R[i][N+m2], -self.TN[m1], -self.TN[m2], other[(m1, i)], other[(m2, i)]])

    def limit_nots(self, lo, hi):
        from pysat.card import CardEnc, EncType
        if hi is not None:
            cnf = CardEnc.atmost(lits=self.TN, bound=hi, top_id=self.nv, encoding=EncType.seqcounter)
            for c in cnf.clauses:
                for l in c: self.nv = max(self.nv, abs(l))
                self.add(c)
        if lo is not None and lo > 0:
            cnf = CardEnc.atleast(lits=self.TN, bound=lo, top_id=self.nv, encoding=EncType.seqcounter)
            for c in cnf.clauses:
                for l in c: self.nv = max(self.nv, abs(l))
                self.add(c)

    def add_mono_links(self):
        rows = list(self.rows)
        for t in rows:
            for t2 in rows:
                if t != t2 and (t & t2) == t:
                    for i in range(self.s):
                        g = N + i
                        self.add([-self.V[(g, t)], self.V[(g, t2)]])

    def add_dominance(self, rows):
        s = self.s
        erows = [t for t in rows if FT[t]]
        zrows = [t for t in rows if not FT[t]]
        for i in range(s):
            g = N + i
            # not replaceable by constant 0 / 1
            self.add([self.V[(g, t)] for t in erows])
            self.add([-self.V[(g, t)] for t in zrows])
            for w in range(g):
                lits = []
                for t in erows:
                    gv = self.V[(g, t)]
                    if w < N:
                        if not (t >> w) & 1:
                            lits.append(gv)
                    else:
                        d = self.new()
                        self.add([-d, gv]); self.add([-d, -self.V[(w, t)]])
                        lits.append(d)
                for t in zrows:
                    gv = self.V[(g, t)]
                    if w < N:
                        if (t >> w) & 1:
                            lits.append(-gv)
                    else:
                        d = self.new()
                        self.add([-d, -gv]); self.add([-d, self.V[(w, t)]])
                        lits.append(d)
                self.add(lits)

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, c):
        self.S.add_clause(c)

    def exactly_one(self, xs):
        self.add(list(xs))
        n = len(xs)
        if n <= 6:
            for a in range(n):
                for b in range(a):
                    self.add([-xs[a], -xs[b]])
        else:
            prev = None
            for idx, x in enumerate(xs):
                if idx < n-1:
                    sv = self.new()
                    self.add([-x, sv])
                    if prev is not None:
                        self.add([-prev, sv]); self.add([-prev, -x])
                    prev = sv
                else:
                    self.add([-prev, -x])

    def add_row(self, t):
        if t in self.rows:
            return
        self.rows.append(t)
        s = self.s
        def val(w):
            if w < N:
                return bool((t>>w)&1)
            return self.V[(w,t)]
        for i in range(s):
            g = N+i
            V = self.new(); self.V[(g,t)] = V
            A = self.new(); B = self.new()
            for j in range(g):
                vj = val(j)
                for X, Y in ((self.L[i][j], A), (self.R[i][j], B)):
                    if vj is True:
                        self.add([-X, Y])
                    elif vj is False:
                        self.add([-X, -Y])
                    else:
                        self.add([-X, -Y, vj]); self.add([-X, Y, -vj])
            TA, TO, TN = self.TA[i], self.TO[i], self.TN[i]
            self.add([-TA, -A, -B, V]); self.add([-TA, A, -V]); self.add([-TA, B, -V])
            self.add([-TO, A, B, -V]); self.add([-TO, -A, V]); self.add([-TO, -B, V])
            if not self.monotone:
                self.add([-TN, A, V]); self.add([-TN, -A, -V])
        out = self.V[(N+s-1, t)]
        self.add([out] if FT[t] else [-out])

    def decode(self, model):
        ms = set(x for x in model if x > 0)
        gates = []
        for i in range(self.s):
            j = [a for a in range(N+i) if self.L[i][a] in ms][0]
            k = [a for a in range(N+i) if self.R[i][a] in ms][0]
            op = 'and' if self.TA[i] in ms else ('or' if self.TO[i] in ms else 'not')
            gates.append((op, j, k))
        return gates

def simulate(gates, t):
    w = [(t>>v)&1 for v in range(N)]
    for op, j, k in gates:
        if op == 'and': w.append(w[j] & w[k])
        elif op == 'or': w.append(w[j] | w[k])
        else: w.append(1 - w[j])
    return w[-1]

def check_all(gates):
    bad = [t for t in range(1<<N) if simulate(gates, t) != FT[t]]
    return bad

def run(s, shard, monotone, solver, init_rows, timeout_total, seed=0, nonot_input=False, log=print):
    random.seed(seed)
    enc = Enc(s, shard=shard, monotone=monotone, solver=solver, nonot_input=nonot_input)
    for t in init_rows:
        enc.add_row(t)
    t0 = time.time()
    it = 0
    while True:
        it += 1
        r = enc.S.solve()
        el = time.time()-t0
        if not r:
            log(f'UNSAT s={s} shard={shard} mono={monotone} rows={len(enc.rows)} iters={it} time={el:.1f}')
            return None
        gates = enc.decode(enc.S.get_model())
        bad = check_all(gates)
        if not bad:
            log(f'SAT s={s} shard={shard} mono={monotone} rows={len(enc.rows)} iters={it} time={el:.1f}')
            log(repr(gates))
            return gates
        random.shuffle(bad)
        for t in bad[:3]:
            enc.add_row(t)
        if it % 20 == 0:
            log(f'  iter {it} rows={len(enc.rows)} time={el:.1f}')

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('-s', type=int, default=19)
    ap.add_argument('--shard', type=int, default=None)
    ap.add_argument('--mono', action='store_true')
    ap.add_argument('--solver', default='cadical195')
    ap.add_argument('--nonotin', action='store_true')
    a = ap.parse_args()
    rows = critical_rows()
    print('critical rows', len(rows), flush=True)
    run(a.s, a.shard, a.mono, a.solver, rows, None, nonot_input=a.nonotin, log=lambda m: print(m, flush=True))
