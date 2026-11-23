import itertools, sys

def graphs(n):
    pairs = list(itertools.combinations(range(n), 2))
    seen = set()
    out = []
    perms = list(itertools.permutations(range(n)))
    for mask in range(1 << len(pairs)):
        es = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        adj = [set() for _ in range(n)]
        for u, v in es:
            adj[u].add(v); adj[v].add(u)
        if any(len(adj[i]) == 0 for i in range(n)):
            continue
        bad = False
        for a, c in itertools.combinations(range(n), 2):
            if len(adj[a] & adj[c]) >= 2:
                bad = True; break
        if bad:
            continue
        canon = min(tuple(sorted(tuple(sorted((p[u], p[v]))) for u, v in es)) for p in perms)
        if canon in seen:
            continue
        seen.add(canon)
        out.append(canon)
    return out

n = int(sys.argv[1])
for g in graphs(n):
    print(n, ",".join("%d%d" % e for e in g))
