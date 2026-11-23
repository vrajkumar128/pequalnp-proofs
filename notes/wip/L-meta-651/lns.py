import sys, time, random
from pysat.solvers import Solver
sys.path.insert(0, '.')
import synth
N = synth.N
FT = synth.FT

def parse_near(path, S):
    out = []
    lines = [l.split() for l in open(path)]
    i = 0
    while i < len(lines):
        p = lines[i]
        if p and p[0] in ('NEAR', 'FOUND'):
            c = [(q[0], int(q[1]), int(q[2])) for q in lines[i+1:i+1+S]]
            if len(c) == S:
                out.append((int(p[1]) if p[0] == 'NEAR' else 0, c))
            i += 1 + S
        else:
            i += 1
    return out

class Bare:
    def __init__(self, s, allow_not=True, rows=None):
        self.s = s
        self.nv = 0
        S = Solver(name='cadical195')
        self.S = S
        L = []; R = []; TA = []; TO = []; TN = []
        for i in range(s):
            g = N + i
            L.append([self.new() for _ in range(g)])
            R.append([self.new() for _ in range(g)])
            TA.append(self.new()); TO.append(self.new()); TN.append(self.new())
        self.L, self.R, self.TA, self.TO, self.TN = L, R, TA, TO, TN
        for i in range(s):
            g = N + i
            self.eo(L[i]); self.eo(R[i]); self.eo([TA[i], TO[i], TN[i]])
            if not allow_not:
                S.add_clause([-TN[i]])
            for j in range(g):
                for k in range(j):
                    S.add_clause([-L[i][j], -R[i][k]])
                S.add_clause([-TN[i], -L[i][j], R[i][j]])
                S.add_clause([TN[i], -L[i][j], -R[i][j]])
        self.allow_not = allow_not
        self.rowset = set()
        rows = rows if rows is not None else range(1 << N)
        for t in rows:
            self.add_row(t)

    def add_row(self, t):
        if t in self.rowset:
            return
        self.rowset.add(t)
        S = self.S; s = self.s
        L, R, TA, TO, TN = self.L, self.R, self.TA, self.TO, self.TN
        allow_not = self.allow_not
        if True:
            V = {}
            for i in range(s):
                g = N + i
                v = self.new(); V[g] = v
                A = self.new(); B = self.new()
                for j in range(g):
                    if j < N:
                        bit = (t >> j) & 1
                        for X, Y in ((L[i][j], A), (R[i][j], B)):
                            S.add_clause([-X, Y] if bit else [-X, -Y])
                    else:
                        for X, Y in ((L[i][j], A), (R[i][j], B)):
                            S.add_clause([-X, -Y, V[j]]); S.add_clause([-X, Y, -V[j]])
                S.add_clause([-TA[i], -A, -B, v]); S.add_clause([-TA[i], A, -v]); S.add_clause([-TA[i], B, -v])
                S.add_clause([-TO[i], A, B, -v]); S.add_clause([-TO[i], -A, v]); S.add_clause([-TO[i], -B, v])
                if allow_not:
                    S.add_clause([-TN[i], A, v]); S.add_clause([-TN[i], -A, -v])
            S.add_clause([V[N + s - 1]] if FT[t] else [-V[N + s - 1]])

    def new(self):
        self.nv += 1
        return self.nv

    def eo(self, xs):
        self.S.add_clause(list(xs))
        n = len(xs)
        prev = None
        for idx, x in enumerate(xs):
            if idx < n - 1:
                sv = self.new()
                self.S.add_clause([-x, sv])
                if prev is not None:
                    self.S.add_clause([-prev, sv]); self.S.add_clause([-prev, -x])
                prev = sv
            else:
                if prev is not None:
                    self.S.add_clause([-prev, -x])

    def fix_lits(self, i, gate):
        op, a, b = gate
        if op == 'not':
            return [self.TN[i], self.L[i][a]]
        if a == b:
            return None
        a, b = min(a, b), max(a, b)
        return [self.TA[i] if op == 'and' else self.TO[i], self.L[i][a], self.R[i][b]]

    def decode(self, model):
        ms = set(x for x in model if x > 0)
        gates = []
        for i in range(self.s):
            j = [a for a in range(N + i) if self.L[i][a] in ms][0]
            k = [a for a in range(N + i) if self.R[i][a] in ms][0]
            op = 'and' if self.TA[i] in ms else ('or' if self.TO[i] in ms else 'not')
            gates.append((op, j, k))
        return gates

def main():
    path = sys.argv[1]
    s = int(sys.argv[2])
    allow_not = int(sys.argv[3])
    ks = [int(x) for x in sys.argv[4].split(',')]
    tries = int(sys.argv[5])
    budget = int(sys.argv[6])
    seed = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    rng = random.Random(seed)
    t0 = time.time()
    import synth as _s
    init = _s.critical_rows() + rng.sample(range(1 << N), 150)
    B = Bare(s, allow_not=bool(allow_not), rows=init)
    print('built', B.nv, round(time.time() - t0, 1), flush=True)
    nears = parse_near(path, s)
    print('near-miss circuits', len(nears), flush=True)
    stats = {'sat': 0, 'unsat': 0, 'unknown': 0}
    for ni, (cost, c) in enumerate(nears):
        fixed = [B.fix_lits(i, g) for i, g in enumerate(c)]
        for k in ks:
            for _ in range(tries):
                free = set(rng.sample(range(s), k))
                free |= {i for i in range(s) if fixed[i] is None}
                assum = []
                for i in range(s):
                    if i not in free:
                        assum += fixed[i]
                while True:
                    B.S.conf_budget(budget)
                    r = B.S.solve_limited(assumptions=assum)
                    if r is None:
                        stats['unknown'] += 1
                        break
                    elif r is False:
                        stats['unsat'] += 1
                        break
                    g = B.decode(B.S.get_model())
                    bad = synth.check_all(g)
                    if not bad:
                        print('FOUND', s, g, flush=True)
                        return
                    stats['cex'] = stats.get('cex', 0) + 1
                    for t in rng.sample(bad, min(3, len(bad))):
                        B.add_row(t)
        print('near', ni, 'cost', cost, stats, round(time.time() - t0), flush=True)

if __name__ == '__main__':
    main()
