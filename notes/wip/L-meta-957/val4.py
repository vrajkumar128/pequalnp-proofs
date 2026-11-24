"""Validation of the C0/C1 virtual rows and of the family bound behind deficit_constraints, on
the Fano plane (q = 2, lines {0,1,3}+w mod 7). With exactly one NOT and s = 14 = 7*2 gates, the
bound gives at least 1 deficit flag; flag-transitivity lets us fix (line 0, point 0).
Expected: (exactly one NOT, s = 14) and (same + deficit >= 1 at flag (0,0)) are both SAT; every
model found is checked: the decoded list's C0 / C1 evaluation must show the claimed deficit."""
import sys, time
sys.path.insert(0, '.')
from cegis957 import *

fano = [sorted({(u + w) % 7 for u in (0, 1, 3)}) for w in range(7)]
tabs = line_tables(7, fano)


def c01(gates, c):
    return [('and', []) if op == 'not' and c else ('or', []) if op == 'not' else (op, ins)
            for op, ins in gates]


def deficits(n, lines, gates, outs):
    W1 = bit_wires(n, c01(gates, 1))
    W0 = bit_wires(n, c01(gates, 0))
    full = (1 << n) - 1
    res = []
    for w, L in enumerate(lines):
        m = full & ~sum(1 << i for i in L)
        t0 = (W1[outs[w]] >> m) & 1
        for u in L:
            if t0 and not ((W0[outs[w]] >> (1 << u)) & 1):
                res.append((w, u))
    return res


for s, mint, flag in ((14, None, None), (14, 1, (0, 0))):
    t0 = time.time()
    ex = deficit_constraints(fano, flag=flag, min_total=mint, n=7) if mint else None
    r = cegis(7, tabs, fano, s, maxnot=1, exact_not=1, init_rows=set(range(128)), extra=ex,
              sb_order=False, sb_distinct=False)
    print('s=%d exact one NOT, deficit>=%s flag %s: %s %.1fs' % (s, mint, flag, r[0], time.time() - t0), flush=True)
    if r[1]:
        g, o = r[1]
        print('  circuit', g, o)
        d = deficits(7, fano, g, o)
        print('  deficit flags (recomputed by evaluation):', d)
        if mint:
            print('  check flag in recomputed deficits:', flag in d, 'count ok:', len(d) >= mint)
