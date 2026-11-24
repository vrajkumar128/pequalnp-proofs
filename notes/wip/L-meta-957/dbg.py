import sys; sys.path.insert(0, '.')
from search957 import *
n = 6
sets = [[0, 1, 2], [0, 3], [1, 4], [2, 5]]
tabs = line_tables(n, sets)
ex = deficit_constraints(sets, flag=(0, 0), min_total=1, n=n)
r = cegis(n, tabs, sets, 9, maxnot=1, exact_not=1, init_rows=set(range(64)), extra=ex, log=lambda m: None)
g, o = r[1]
print(r[0]); 
for j, gg in enumerate(g): print(n + j, gg)
print('outs', o)
W1 = bit_wires(n, c01(g, 1)); W0 = bit_wires(n, c01(g, 0))
full = 63
fams = {}
for w, S in enumerate(sets):
    m = full & ~sum(1 << i for i in S)
    t0 = (W1[o[w]] >> m) & 1
    A0 = [u for u in range(n) if (W0[o[w]] >> (1 << u)) & 1]
    P1o = [u for u in range(n) if (W1[o[w]] >> (1 << u)) & 1]
    print('set', w, S, 'type0' if t0 else 'type1', 'A0', A0, 'P1(out)', P1o)
    for wi, W in ((1, W1), (0, W0)):
        F = []
        for j in range(len(g)):
            P = [u for u in range(n) if (W[n + j] >> (1 << u)) & 1]
            if not ((W[n + j] >> m) & 1) and len(P) >= 2:
                F.append((n + j, P))
        print('   F%d:' % wi, F)
