import itertools
from functools import lru_cache

def norm(E):
    return frozenset(frozenset(e) for e in E)

def tau(E):
    E = [tuple(e) for e in E]
    if not E: return 0
    # branch on an edge
    best = [len(E)]
    def rec(E, k):
        if k >= best[0]: return
        if not E:
            best[0] = k; return
        u, v = E[0]
        rec([e for e in E if u not in e], k+1)
        rec([e for e in E if v not in e], k+1)
    rec(E, 0)
    return best[0]

def adj(E):
    d = {}
    for e in E:
        u, v = tuple(e)
        d.setdefault(u, set()).add(v); d.setdefault(v, set()).add(u)
    return d

def is_forest(E):
    par = {}
    def find(x):
        while par.get(x, x) != x: x = par[x]
        return x
    for e in E:
        u, v = tuple(e)
        a, b = find(u), find(v)
        if a == b: return False
        par[a] = b
    return True

def girth(E):
    A = adj(E); best = 10**9
    for s in A:
        dist = {s: 0}; parent = {s: None}; q = [s]
        for x in q:
            for y in A[x]:
                if y not in dist:
                    dist[y] = dist[x]+1; parent[y] = x; q.append(y)
                elif parent[x] != y:
                    best = min(best, dist[x]+dist[y]+1)
    return best

def dists(E, s):
    A = adj(E); dist = {s: 0}; q = [s]
    for x in q:
        for y in A.get(x, ()):
            if y not in dist: dist[y] = dist[x]+1; q.append(y)
    return dist

def in522(E):
    if girth(E) < 7: return False
    A = adj(E)
    hubs = [v for v in A if len(A[v]) >= 3]
    for u in hubs:
        d = dists(E, u)
        for v in hubs:
            if v != u and v in d and d[v] < 7: return False
    return True

def mu(E, Aset):
    return len(Aset) + len(E) + tau(E) - 1

def provable(E, Aset=()):
    # True if the bound mu is a proven lower bound by: A-elim, forests, 522 class, cheap leaf
    E = norm(E)
    if not E: return True
    if is_forest(E): return True
    if in522(E): return True
    A = adj(E)
    t = tau(E)
    for l in A:
        if len(A[l]) == 1:
            E2 = frozenset(e for e in E if l not in e)
            if tau(E2) == t and provable(E2): return True
    return False

def restrict(E, v, b):
    E = norm(E)
    A = adj(E)
    if b == 0:
        return frozenset(e for e in E if v not in e), set()
    N = A.get(v, set())
    E2 = frozenset(e for e in E if v not in e and not (e & N))
    return E2, set(N)
