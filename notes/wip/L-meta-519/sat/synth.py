import sys, itertools, time, random
from pysat.solvers import Solver

def edge_fn(n, edges):
    def f(r):
        return any(((r>>u)&1) and ((r>>v)&1) for u,v in edges)
    return f

class Synth:
    def __init__(self, n, s, f, solver='cadical195', symbreak=True, allow_not=True):
        self.n, self.s, self.f = n, s, f
        self.nv = 0
        self.S = Solver(name=solver)
        self.sel = {}   # gate i -> list of (var, op, ins)
        for i in range(n, n+s):
            opts = []
            for j in (range(i) if allow_not else []):
                opts.append((self.new(), 'not', (j,)))
            for j in range(i):
                for k in range(j+1, i):
                    opts.append((self.new(), 'and', (j,k)))
                    opts.append((self.new(), 'or', (j,k)))
            self.sel[i] = opts
            vs = [o[0] for o in opts]
            self.S.add_clause(vs)
            # at most one (pairwise is too big; use sequential counter)
            self.amo(vs)
        self.used = {}
        if symbreak:
            # every non-output gate is used by a later gate
            for i in range(n, n+s-1):
                users = []
                for i2 in range(i+1, n+s):
                    for (v,op,ins) in self.sel[i2]:
                        if i in ins: users.append(v)
                self.S.add_clause(users)
            # no NOT of NOT
            for i in range(n, n+s):
                for (v,op,ins) in self.sel[i]:
                    if op=='not' and ins[0]>=n:
                        for (v2,op2,ins2) in self.sel[ins[0]]:
                            if op2=='not': self.S.add_clause([-v,-v2])
            # lex order on independent consecutive gates
            opcode = {'not':0,'and':1,'or':2}
            def key(o):
                v,op,ins = o
                return (ins[-1], ins[0], opcode[op])
            for i in range(n, n+s-1):
                A = self.sel[i]; B = self.sel[i+1]
                for o1 in A:
                    k1 = key(o1)
                    for o2 in B:
                        if i in o2[2]: continue
                        if key(o2) < k1:
                            self.S.add_clause([-o1[0], -o2[0]])
            # no duplicate gates
            for i in range(n, n+s):
                for i2 in range(i+1, n+s):
                    d = {(o[1],o[2]): o[0] for o in self.sel[i2]}
                    for o in self.sel[i]:
                        if (o[1],o[2]) in d: self.S.add_clause([-o[0], -d[(o[1],o[2])]])
        self.rows = {}
    def new(self):
        self.nv += 1
        return self.nv
    def amo(self, vs):
        # sequential counter
        if len(vs) <= 1: return
        prev = None
        for idx, x in enumerate(vs):
            if idx == len(vs)-1:
                if prev is not None: self.S.add_clause([-x, -prev])
                break
            s = self.new()
            self.S.add_clause([-x, s])
            if prev is not None:
                self.S.add_clause([-prev, s])
                self.S.add_clause([-x, -prev])
            prev = s
    def add_row(self, r):
        n = self.n
        val = {}
        for j in range(n):
            val[j] = bool((r>>j)&1)
        for i in range(n, n+self.s):
            val[i] = self.new()
        out = self.n + self.s - 1
        fv = self.f(r)
        self.S.add_clause([val[out] if fv else -val[out]])
        def lit(x, pos=True):
            # returns ('c', bool) or ('v', literal)
            if isinstance(x, bool):
                return ('c', x if pos else (not x))
            return ('v', x if pos else -x)
        def clause(sv, lits):
            # clause: -sv OR lits ; lits list of ('c',b)/('v',l)
            cl = [-sv]
            for t, l in lits:
                if t == 'c':
                    if l: return
                else:
                    cl.append(l)
            self.S.add_clause(cl)
        for i in range(n, n+self.s):
            gi = val[i]
            for (sv, op, ins) in self.sel[i]:
                if op == 'not':
                    a = val[ins[0]]
                    # gi <-> not a
                    clause(sv, [lit(gi), lit(a)])
                    clause(sv, [lit(gi, False), lit(a, False)])
                elif op == 'and':
                    a, b = val[ins[0]], val[ins[1]]
                    clause(sv, [lit(gi, False), lit(a)])
                    clause(sv, [lit(gi, False), lit(b)])
                    clause(sv, [lit(gi), lit(a, False), lit(b, False)])
                else:
                    a, b = val[ins[0]], val[ins[1]]
                    clause(sv, [lit(gi), lit(a, False)])
                    clause(sv, [lit(gi), lit(b, False)])
                    clause(sv, [lit(gi, False), lit(a), lit(b)])
        self.rows[r] = val
    def extract(self, model):
        ms = set(l for l in model if l > 0)
        circ = []
        for i in range(self.n, self.n+self.s):
            for (sv, op, ins) in self.sel[i]:
                if sv in ms:
                    circ.append((op, ins)); break
        return circ

def evalc(n, circ, r):
    vals = [bool((r>>j)&1) for j in range(n)]
    for op, ins in circ:
        if op == 'not': vals.append(not vals[ins[0]])
        elif op == 'and': vals.append(vals[ins[0]] and vals[ins[1]])
        else: vals.append(vals[ins[0]] or vals[ins[1]])
    return vals[-1]

def synth(n, s, f, init_rows=None, verbose=True, timeout=None, allow_not=True, every=1):
    sy = Synth(n, s, f, allow_not=allow_not)
    rows = list(init_rows or [])
    for r in rows: sy.add_row(r)
    it = 0
    t0 = time.time()
    while True:
        it += 1
        ok = sy.S.solve()
        if not ok:
            if verbose: print(f'UNSAT after {it} iters, {len(sy.rows)} rows, {time.time()-t0:.1f}s', flush=True)
            return None
        circ = sy.extract(sy.S.get_model())
        bad = [r for r in range(1<<n) if evalc(n, circ, r) != f(r)]
        if not bad:
            if verbose: print(f'SAT after {it} iters, {len(sy.rows)} rows, {time.time()-t0:.1f}s', flush=True)
            return circ
        # add a few bad rows
        random.shuffle(bad)
        for r in bad[:2]:
            sy.add_row(r)
        if verbose and it % every == 0: print(f' iter {it} rows {len(sy.rows)} t {time.time()-t0:.1f}', flush=True)

def init_rows_for(n, edges):
    rows = [0]
    for u,v in edges: rows.append((1<<u)|(1<<v))
    return rows

if __name__ == '__main__':
    pass
