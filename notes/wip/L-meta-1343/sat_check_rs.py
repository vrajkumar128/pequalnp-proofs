import sys, time, random
sys.path.insert(0, '.')
import shard_search as S
import brute_check as BC
n = int(sys.argv[1]); smax = int(sys.argv[2]); lim = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
t0 = time.time(); mism = 0; checked = 0
gs = BC.graphs_upto_iso(n)
random.seed(1); random.shuffle(gs)
for edges in gs[:lim]:
    if len(set(v for e in edges for v in e)) < n: continue
    for D in [None] + S.maximal_independent_sets(n, edges):
        S.OPTS.clear()
        sa, ca, ra = S.min_size(n, edges, D, smax=smax, enc='A')
        S.OPTS.clear(); S.OPTS['rs'] = {'P1', 'P2', 'P1Q1', 'MIS'}
        sr, cr, rr = S.min_size(n, edges, D, smax=smax, enc='B')
        S.OPTS.clear()
        checked += 1
        flag = 'OK' if sa == sr else 'MISMATCH'
        if sa != sr: mism += 1
        print(flag, n, edges, D, sa, sr, '%.0fs' % (time.time() - t0), flush=True)
print('sat rs check: checked %d, mismatches %d, %.1fs' % (checked, mism, time.time() - t0))
