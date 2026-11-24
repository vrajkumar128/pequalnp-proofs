import itertools, sys
sys.path.insert(0, '.')
from compute import formula, pet, k44
# Exact Lean PCDerivable closure: polynomials NOT reduced (x^2 is a separate monomial),
# generators: Boolean axioms X v*X v + X v and clause polys of totalDegree <= B; closure under
# + and p -> X j * p when totalDegree(X j * p) <= B.
def pc_exact(F, B):
    vars_ = sorted({l[0] for C in F for l in C}); idx = {v: i for i, v in enumerate(vars_)}; n = len(vars_)
    mons = []
    for d in range(B + 1):
        mons.extend(itertools.combinations_with_replacement(range(n), d))
    mid = {m: i for i, m in enumerate(mons)}; deg = [len(m) for m in mons]
    piv = {}; queue = []
    def insert(row):
        while row:
            p = row.bit_length() - 1
            if p in piv: row ^= piv[p]
            else:
                piv[p] = row
                if deg[p] <= B - 1: queue.append(row)
                return
    for i in range(n):
        insert((1 << mid[(i, i)]) ^ (1 << mid[(i,)]))
    for C in F:
        if len(C) <= B:
            res = {(): 1}
            for (v, s) in C:
                i = idx[v]; nr = {}
                for m in res:
                    for t in ([tuple(sorted(m + (i,)))] + ([m] if s else [])):
                        nr[t] = nr.get(t, 0) ^ 1
                res = {m: 1 for m, c in nr.items() if c}
            row = 0
            for m in res: row ^= 1 << mid[m]
            insert(row)
    while queue:
        row = queue.pop(); ml = []; r = row
        while r:
            p = r.bit_length() - 1; ml.append(p); r ^= 1 << p
        for j in range(n):
            out = 0
            for p in ml: out ^= 1 << mid[tuple(sorted(mons[p] + (j,)))]
            insert(out)
    r = 1 << mid[()]
    while r:
        p = r.bit_length() - 1
        if p in piv: r ^= piv[p]
        else: return False
    return True
Fp = formula(10, pet, 5); Fk = formula(8, k44, 3)
for name, F, B in [('Petersen', Fp, 2), ('Petersen', Fp, 3), ('K44', Fk, 2), ('K44', Fk, 3), ('K44', Fk, 4)]:
    print(name, 'exact Lean PC degree', B, pc_exact(F, B)); sys.stdout.flush()
