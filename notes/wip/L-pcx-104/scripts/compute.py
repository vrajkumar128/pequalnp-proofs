import itertools, sys

def formula(n, edges, K):
    # literal: (var, bool); var: ('x',i) or ('s',h,j)
    F = []
    for (u, v) in edges:
        F.append(frozenset({(('x', u), True), (('x', v), True)}))
    for i in range(n):
        if i + 1 < n:
            F.append(frozenset({(('x', i), False), (('s', i, 0), True)}))
    for i in range(1, n):
        h = i - 1
        if i + 1 < n:
            for j in range(K):
                F.append(frozenset({(('s', h, j), False), (('s', i, j), True)}))
            for g in range(K - 1):
                F.append(frozenset({(('x', i), False), (('s', h, g), False), (('s', i, g + 1), True)}))
        F.append(frozenset({(('x', i), False), (('s', h, K - 1), False)}))
    for j in range(1, K):
        F.append(frozenset({(('s', 0, j), False)}))
    return list(set(F))

def width_sat(F, k):
    S = set(C for C in F if len(C) <= k)
    frontier = list(S)
    bylit = {}
    for C in S:
        for l in C:
            bylit.setdefault(l, []).append(C)
    while frontier:
        new = []
        for C in frontier:
            for (v, s) in C:
                for D in list(bylit.get((v, not s), [])):
                    P, N = (C, D) if s else (D, C)
                    R = (P - {(v, True)}) | (N - {(v, False)})
                    if len(R) <= k and R not in S:
                        S.add(R); new.append(R)
                        for l in R:
                            bylit.setdefault(l, []).append(R)
                        if len(R) == 0:
                            return True, len(S)
        frontier = new
    return frozenset() in S, len(S)

def pc_refutable(F, B):
    vars_ = sorted({l[0] for C in F for l in C})
    idx = {v: i for i, v in enumerate(vars_)}
    n = len(vars_)
    mons = []
    for d in range(B + 1):
        mons.extend(itertools.combinations(range(n), d))
    mid = {m: i for i, m in enumerate(mons)}  # graded: higher degree -> higher index
    deg = [len(m) for m in mons]
    def poly_of_clause(C):
        # product of (1+x) for positive, x for negative ; dict of monomial sets
        p = {(): 1}
        res = {frozenset(): 1}
        for (v, s) in C:
            i = idx[v]
            nr = {}
            for m in res:
                terms = [m | {i}] + ([m] if s else [])
                for t in terms:
                    nr[t] = nr.get(t, 0) ^ 1
            res = {m: 1 for m, c in nr.items() if c}
        row = 0
        for m in res:
            row ^= 1 << mid[tuple(sorted(m))]
        return row
    piv = {}
    queue = []
    def insert(row):
        while row:
            p = row.bit_length() - 1
            if p in piv:
                row ^= piv[p]
            else:
                piv[p] = row
                if deg[p] <= B - 1:
                    queue.append(row)
                return True
        return False
    for C in F:
        if len(C) <= B:
            insert(poly_of_clause(C))
    # precompute multiplication tables for monomials of degree <= B-1
    mult = {}
    while queue:
        row = queue.pop()
        mlist = []
        r = row
        while r:
            p = r.bit_length() - 1
            mlist.append(p); r ^= 1 << p
        for j in range(n):
            out = 0
            for p in mlist:
                m = mons[p]
                if j in m:
                    out ^= 1 << p
                else:
                    out ^= 1 << mid[tuple(sorted(m + (j,)))]
            insert(out)
        if 0 in piv:
            pass
    # is 1 in span?
    one = 1 << mid[()]
    r = one
    while r:
        p = r.bit_length() - 1
        if p in piv:
            r ^= piv[p]
        else:
            return False, len(piv), len(mons)
    return True, len(piv), len(mons)

pet = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
k44 = [(a, b) for a in range(4) for b in range(4, 8)]
if __name__ == "__main__":
    Fp = formula(10, pet, 5)
    Fk = formula(8, k44, 3)
    print('Petersen clauses', len(Fp), 'vars', len({l[0] for C in Fp for l in C}))
    print('K44 clauses', len(Fk), 'vars', len({l[0] for C in Fk for l in C}))
    for name, F in [('Petersen', Fp), ('K44', Fk)]:
        for k in [1, 2, 3]:
            print(name, 'width', k, width_sat(F, k)); sys.stdout.flush()
    for name, F, Bs in [('Petersen', Fp, [2, 3]), ('K44', Fk, [2, 3, 4])]:
        for B in Bs:
            print(name, 'PC degree', B, pc_refutable(F, B)); sys.stdout.flush()
