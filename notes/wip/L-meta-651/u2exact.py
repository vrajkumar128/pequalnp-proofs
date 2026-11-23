import sys, time, itertools
from pysat.solvers import Solver

def synth_u2(n, ft, s, budget=None):
    S = Solver(name='cadical195')
    nv = [0]
    def new():
        nv[0] += 1
        return nv[0]
    sel = []
    for i in range(s):
        g = n + i
        d = {}
        for j in range(g):
            for k in range(j + 1, g):
                d[(j, k)] = new()
        sel.append(d)
        S.add_clause(list(d.values()))
        vs = list(d.values())
        # AMO via sequential
        prev = None
        for idx, x in enumerate(vs):
            if idx < len(vs) - 1:
                sv = new()
                S.add_clause([-x, sv])
                if prev is not None:
                    S.add_clause([-prev, sv]); S.add_clause([-prev, -x])
                prev = sv
            elif prev is not None:
                S.add_clause([-prev, -x])
    F = [[new() for _ in range(4)] for _ in range(s)]
    for i in range(s):
        f = F[i]
        # gate f(a,b) with f[2a+b]; forbid constants, projections, xor/xnor: allowed = and-type (odd number of ones)
        for bits in itertools.product([0, 1], repeat=4):
            if sum(bits) % 2 == 0:
                S.add_clause([(-f[q] if bits[q] else f[q]) for q in range(4)])
    for i in range(s - 1):
        g = n + i
        S.add_clause([sel[i2][(j, k)] for i2 in range(i + 1, s) for (j, k) in sel[i2] if k == g or j == g])
    V = {}
    for t in range(1 << n):
        for i in range(s):
            V[(n + i, t)] = new()
        def val(w):
            if w < n:
                return bool((t >> w) & 1)
            return V[(w, t)]
        for i in range(s):
            g = n + i
            v = V[(g, t)]
            for (j, k), x in sel[i].items():
                vj, vk = val(j), val(k)
                for a in (0, 1):
                    for b in (0, 1):
                        cl = [-x]
                        if vj is True or vj is False:
                            if int(vj) != a:
                                continue
                        else:
                            cl.append(-vj if a else vj)
                        if vk is True or vk is False:
                            if int(vk) != b:
                                continue
                        else:
                            cl.append(-vk if b else vk)
                        S.add_clause(cl + [-F[i][2 * a + b], v])
                        S.add_clause(cl + [F[i][2 * a + b], -v])
        out = V[(n + s - 1, t)]
        S.add_clause([out] if ft[t] else [-out])
    r = S.solve()
    return r

def graph_ft(n, edges):
    return [1 if any(((t >> a) & 1) and ((t >> b) & 1) for a, b in edges) else 0 for t in range(1 << n)]

if __name__ == '__main__':
    tests = {
        'C5': (5, [(i, (i + 1) % 5) for i in range(5)]),
        'C6': (6, [(i, (i + 1) % 6) for i in range(6)]),
        'P4': (4, [(0, 1), (1, 2), (2, 3)]),
        'K3': (3, [(0, 1), (1, 2), (0, 2)]),
        'Pet-4': None,
    }
    for name in sys.argv[1:]:
        n, E = tests[name]
        ft = graph_ft(n, E)
        for s in range(1, 20):
            t0 = time.time()
            r = synth_u2(n, ft, s)
            print(name, s, r, round(time.time() - t0, 1), flush=True)
            if r:
                break
