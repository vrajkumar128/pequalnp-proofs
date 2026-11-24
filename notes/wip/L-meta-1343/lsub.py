import sys, time
sys.path.insert(0, '.')
import shard_search as S
S.OPTS.clear(); S.OPTS['rs'] = set(sys.argv[1].split(','))
G = S.MAIN_EDGES
adj = {v: set() for v in range(11)}
for u, v in G: adj[u].add(v); adj[v].add(u)
order = sorted(range(11), key=lambda v: -len(adj[v]))
for v in order:
    gone = adj[v] | {v}
    H = [(a, b) for (a, b) in G if a not in gone and b not in gone]
    t = time.time()
    L = S.least_size(H)
    print('v=%d deg=%d |V(H)|=%d |E(H)|=%d L=%d time=%.1fs' % (v, len(adj[v]), len(set(x for e in H for x in e)), len(H), L, time.time() - t), flush=True)
