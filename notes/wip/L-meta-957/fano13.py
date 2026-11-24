import sys, time
sys.path.insert(0, '/tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-meta-957')
from search957 import *
tabs = line_tables(7, FANO)
for perline in (False, True):
    t0 = time.time()
    ex = family_constraints(FANO, flag=(0, 0), min_total=2, n=7, perline=perline)
    r = cegis(7, tabs, FANO, 13, maxnot=1, init_rows=set(range(128)), extra=ex, log=lambda m: None)
    print('Fano one-NOT s=13 (covers <= 13), family bound, perline=%s, flag (0,0): %s %.1fs' % (perline, r[0], time.time() - t0), flush=True)
