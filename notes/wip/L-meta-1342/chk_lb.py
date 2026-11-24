import sys, time
sys.path.insert(0, '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-1342')
import junk_shard as J
J.OPTS.clear(); J.OPTS['rs'] = {'P1', 'P2', 'MIS', 'P1Q1'}; J.OPTS['rsrec'] = True
for key in sys.argv[1:]:
    k, c = eval(key)
    for size in range(J.LTABLE[key] - 1, 0, -1):
        t0 = time.time()
        cnf, meta = J.encode(k, list(c), size, None)
        r, m = J.solve_pysat(cnf)
        print('%s size=%d %s %.1fs' % (key, size, 'SAT' if r else 'UNSAT', time.time() - t0), flush=True)
