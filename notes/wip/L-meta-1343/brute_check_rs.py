import sys, time
sys.path.insert(0, '.')
import shard_search as S
import brute_check as BC
n = int(sys.argv[1]); smax = int(sys.argv[2])
t0 = time.time(); mism = 0; checked = 0
for edges in BC.graphs_upto_iso(n):
    for D in [None] + S.maximal_independent_sets(n, edges):
        sb, cb = BC.min_brute(n, edges, D, smax)
        S.OPTS.clear(); S.OPTS['rs'] = {'P1', 'P2', 'P1Q1', 'MIS'}
        sr, cr, rr = S.min_size(n, edges, D, smax=smax, enc='B')
        S.OPTS.clear()
        checked += 1
        if sb != sr:
            mism += 1
            print('MISMATCH', n, edges, D, sb, sr, flush=True)
print('rs check: checked %d, mismatches %d, %.1fs' % (checked, mism, time.time() - t0))
