import sys, time
sys.path.insert(0, '.')
from cegis957 import *
fano = [sorted({(u + w) % 7 for u in (0, 1, 3)}) for w in range(7)]
tabs = line_tables(7, fano)
for s, mn, so, sd in ((14, 0, 1, 1), (14, 0, 0, 0), (14, 1, 1, 1)):
    t0 = time.time()
    r = cegis(7, tabs, fano, s, maxnot=mn, init_rows=set(range(128)), sb_order=bool(so), sb_distinct=bool(sd))
    print(s, mn, so, sd, r[0], r[3], '%.1fs' % (time.time() - t0), flush=True)
    if r[1]: print(r[1])
