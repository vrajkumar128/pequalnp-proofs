import sys, time, random
sys.path.insert(0, '.')
from graphs import *
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

AND, OR, NOT = 0, 1, 2

class Enc:
    def __init__(self, n, s, allow_not=True, solver='cadical195'):
        self.n, self.s = n, s
        self.nv = 0
        self.S = Solver(name=solver)
        self.gates = range(n, n+s)
        self.A = {}; self.B = {}; self.T = {}
        for i in self.gates:
            self.A[i] = {j: self.new() for j in range(i)}
            self.B[i] = {j: self.new() for j in range(i)}
            self.T[i] = [self.new(), self.new(), self.new()]
            self.exactly_one(list(self.A[i].values()))
            self.exactly_one(list(self.B[i].values()))
            self.exactly_one(self.T[i])
            if not allow_not: self.S.add_clause([-self.T[i][NOT]])
            # a <= b ; a == b iff NOT
            for ja in range(i):
                for jb in range(ja):
                    self.S.add_clause([-self.A[i][ja], -self.B[i][jb]])
                # a == b -> NOT ; NOT -> a == b
                self.S.add_clause([-self.A[i][ja], -self.B[i][ja], self.T[i][NOT]])
                self.S.add_clause([-self.A[i][ja], -self.T[i][NOT], self.B[i][ja]])
        n_, s_ = n, s
        last = n + s - 1
        # every non-output gate used
        for i in self.gates:
            if i == last: continue
            self.S.add_clause([self.A[i2][i] for i2 in range(i+1, n+s)] + [self.B[i2][i] for i2 in range(i+1, n+s)])
        # no NOT of NOT
        for i in self.gates:
            for j in range(n, i):
                self.S.add_clause([-self.T[i][NOT], -self.A[i][j], -self.T[j][NOT]])
        # lex order of consecutive independent gates: key (b, a, op)
        for i in range(n, n+s-1):
            i2 = i + 1
            for x in range(i):
                for y in range(i2):
                    if y == i: continue
                    if x > y:
                        self.S.add_clause([-self.B[i][x], -self.B[i2][y]])
                    elif x == y:
                        # same b: need (a_i, op_i) < (a_i2, op_i2)
                        for ax in range(x+1):
                            for ay in range(x+1):
                                if ax > ay:
                                    self.S.add_clause([-self.B[i][x], -self.B[i2][y], -self.A[i][ax], -self.A[i2][ay]])
                                elif ax == ay:
                                    for o1 in range(3):
                                        for o2 in range(3):
                                            if o1 >= o2:
                                                self.S.add_clause([-self.B[i][x], -self.B[i2][y], -self.A[i][ax], -self.A[i2][ay], -self.T[i][o1], -self.T[i2][o2]])
        # no duplicates at all
        for i in self.gates:
            for i2 in range(i+2, n+s):
                for bx in range(i):
                    for ax in range(bx+1):
                        for o in range(3):
                            self.S.add_clause([-self.A[i][ax], -self.B[i][bx], -self.A[i2][ax], -self.B[i2][bx], -self.T[i][o], -self.T[i2][o]])
        self.rows = set()
    def new(self):
        self.nv += 1; return self.nv
    def exactly_one(self, vs):
        self.S.add_clause(vs)
        enc = CardEnc.atmost(lits=vs, bound=1, top_id=self.nv, encoding=EncType.seqcounter)
        for cl in enc.clauses: self.S.add_clause(cl)
        self.nv = max(self.nv, enc.nv)
    def add_row(self, r, fv):
        n = self.n
        val = {}
        for j in range(n): val[j] = bool((r >> j) & 1)
        for i in self.gates: val[i] = self.new()
        S = self.S
        for i in self.gates:
            in1, in2, out = self.new(), self.new(), val[i]
            for (sel, inn) in ((self.A[i], in1), (self.B[i], in2)):
                for j, sv in sel.items():
                    vj = val[j]
                    if vj is True: S.add_clause([-sv, inn])
                    elif vj is False: S.add_clause([-sv, -inn])
                    else:
                        S.add_clause([-sv, -vj, inn]); S.add_clause([-sv, vj, -inn])
            ta, to, tn = self.T[i]
            S.add_clause([-ta, -out, in1]); S.add_clause([-ta, -out, in2]); S.add_clause([-ta, out, -in1, -in2])
            S.add_clause([-to, out, -in1]); S.add_clause([-to, out, -in2]); S.add_clause([-to, -out, in1, in2])
            S.add_clause([-tn, out, in1]); S.add_clause([-tn, -out, -in1])
        last = n + self.s - 1
        S.add_clause([val[last] if fv else -val[last]])
        self.rows.add(r)
    def add_elim(self, assign, maxkill):
        n = self.n; S = self.S
        if maxkill < 0: S.add_clause([]); return
        if maxkill >= self.s: return
        K, C = {}, {}
        for i in self.gates:
            K[i] = self.new(); C[(i,0)] = self.new(); C[(i,1)] = self.new()
            P = {}
            for which, sel in ((1, self.A[i]), (2, self.B[i])):
                for c in (0, 1):
                    P[(which, c)] = self.new()
                for j, sv in sel.items():
                    if j in assign:
                        S.add_clause([-sv, P[(which, assign[j])]])
                    elif j >= n:
                        for c in (0,1):
                            S.add_clause([-sv, -C[(j,c)], P[(which, c)]])
            for which in (1,2):
                for c in (0,1):
                    S.add_clause([-P[(which,c)], K[i]])
            ta, to, tn = self.T[i]
            # AND
            S.add_clause([-ta, -P[(1,0)], C[(i,0)]]); S.add_clause([-ta, -P[(2,0)], C[(i,0)]])
            S.add_clause([-ta, -P[(1,1)], -P[(2,1)], C[(i,1)]])
            # OR
            S.add_clause([-to, -P[(1,1)], C[(i,1)]]); S.add_clause([-to, -P[(2,1)], C[(i,1)]])
            S.add_clause([-to, -P[(1,0)], -P[(2,0)], C[(i,0)]])
            # NOT
            S.add_clause([-tn, -P[(1,0)], C[(i,1)]]); S.add_clause([-tn, -P[(1,1)], C[(i,0)]])
        lits = [K[i] for i in self.gates]
        if getattr(self, 'dead', False):
            last = n + self.s - 1
            Dd = {}
            for i in self.gates:
                if i != last: Dd[i] = self.new()
            for i in reversed(list(self.gates)):
                if i == last: continue
                terms = []
                for i2 in range(i+1, n+self.s):
                    w = self.new()
                    S.add_clause([-w, self.A[i2][i], self.B[i2][i]])
                    S.add_clause([-w, -C[(i2,0)]]); S.add_clause([-w, -C[(i2,1)]])
                    if i2 != last: S.add_clause([-w, -Dd[i2]])
                    terms.append(w)
                S.add_clause([Dd[i]] + terms)
            lits = []
            for i in self.gates:
                if i == last: lits.append(K[i]); continue
                r = self.new()
                S.add_clause([-K[i], r]); S.add_clause([-Dd[i], r])
                lits.append(r)
        enc = CardEnc.atmost(lits=lits, bound=maxkill, top_id=self.nv, encoding=EncType.seqcounter)
        for cl in enc.clauses: S.add_clause(cl)
        self.nv = max(self.nv, enc.nv)
    def extract(self, model):
        ms = set(l for l in model if l > 0)
        circ = []
        for i in self.gates:
            a = [j for j, v in self.A[i].items() if v in ms][0]
            b = [j for j, v in self.B[i].items() if v in ms][0]
            t = [k for k in range(3) if self.T[i][k] in ms][0]
            circ.append(('not', (a,)) if t == NOT else (('and' if t == AND else 'or'), (a, b)))
        return circ

def evalc(n, circ, r):
    vals = [bool((r>>j)&1) for j in range(n)]
    for op, ins in circ:
        if op == 'not': vals.append(not vals[ins[0]])
        elif op == 'and': vals.append(vals[ins[0]] and vals[ins[1]])
        else: vals.append(vals[ins[0]] or vals[ins[1]])
    return vals[-1]

def restrict_multi(E, assign):
    E = norm(E); A = set()
    Ad = adj(E)
    ones = [v for v,b in assign.items() if b == 1]
    for v in ones:
        for w in Ad.get(v, ()):
            if assign.get(w) == 1: return None
    for v in ones:
        for w in Ad.get(v, ()):
            if assign.get(w) is None: A.add(w)
    dead = set(assign) | A
    E2 = frozenset(e for e in E if not (e & dead))
    return E2, A

def solve(n, E, s, allow_not=True, elim=1, allrows=True, verbose=True, seed=0, dead=False):
    random.seed(seed)
    def f(r): return any(((r>>u)&1) and ((r>>v)&1) for u,v in E)
    t0 = time.time()
    enc = Enc(n, s, allow_not=allow_not)
    enc.dead = dead
    cons = 0
    if elim >= 1:
        assigns = [{v:b} for v in range(n) for b in (0,1)]
        if elim >= 2:
            assigns += [{v:b, w:c} for v in range(n) for w in range(v+1, n) for b in (0,1) for c in (0,1)]
        for a in assigns:
            rr = restrict_multi(E, a)
            if rr is None: continue
            E2, A2 = rr
            if not (E2 or A2): continue
            if provable(E2, A2):
                enc.add_elim(a, s - mu(E2, A2)); cons += 1
    rows = list(range(1 << n)) if allrows else init_rows_for_E(n, E)
    for r in rows: enc.add_row(r, f(r))
    if verbose: print(f'n {n} mu {mu(E,())} s {s} elim {elim} cons {cons} vars {enc.nv} build {time.time()-t0:.1f}s', flush=True)
    it = 0
    while True:
        it += 1
        ok = enc.S.solve()
        if not ok:
            print(f'UNSAT it {it} rows {len(enc.rows)} t {time.time()-t0:.1f}s', flush=True); return None
        circ = enc.extract(enc.S.get_model())
        bad = [r for r in range(1<<n) if evalc(n, circ, r) != f(r)]
        if not bad:
            print(f'SAT it {it} t {time.time()-t0:.1f}s', circ, flush=True); return circ
        random.shuffle(bad)
        for r in bad[:4]: enc.add_row(r, f(r))
        if verbose and it % 10 == 0: print(f' it {it} rows {len(enc.rows)} t {time.time()-t0:.1f}', flush=True)

def init_rows_for_E(n, E):
    rows = [0]
    for u,v in E: rows.append((1<<u)|(1<<v))
    return rows

def cyc_leaves(m, hubs):
    E = [(i,(i+1)%m) for i in range(m)]
    for t,h in enumerate(hubs): E.append((h, m+t))
    return (m+len(hubs), E)

G = {
  'C4': (4, [(0,1),(1,2),(2,3),(3,0)]),
  'C5': (5, [(i,(i+1)%5) for i in range(5)]),
  'C6': (6, [(i,(i+1)%6) for i in range(6)]),
  'C7': (7, [(i,(i+1)%7) for i in range(7)]),
  'P5': (5, [(0,1),(1,2),(2,3),(3,4)]),
  'G4': cyc_leaves(7, [0,3,6]),
  'G5': cyc_leaves(7, [0,1,2,3,4]),
  'C8L': cyc_leaves(8, [0,3,6,7]),
  'C9L': cyc_leaves(9, [0,3,6]),
}
def _main():
    which = sys.argv[1]; s = int(sys.argv[2]); mode = sys.argv[3]; elim = int(sys.argv[4]); allrows = sys.argv[5] == 'all'
    n, E = G[which]
    solve(n, E, s, allow_not=(mode == 'full'), elim=elim, allrows=allrows, dead=(len(sys.argv) > 6 and sys.argv[6] == 'dead'))

def theta(l1,l2,l3):
    E=[]; nxt=2
    for L in (l1,l2,l3):
        prev=0
        for k in range(L-1):
            E.append((prev,nxt)); prev=nxt; nxt+=1
        E.append((prev,1))
    return nxt, E
G['T344'] = theta(3,4,4)
G['T444'] = theta(4,4,4)
G['C7L1'] = cyc_leaves(7, [0])
G['C7L03'] = cyc_leaves(7, [0,3])

if __name__ == '__main__':
    _main()
