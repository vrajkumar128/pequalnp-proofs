import sys, time
sys.path.insert(0, '.')
from cegis957 import *
n = 13
tabs = line_tables()
# sanity: plain circuit verifies
g, o = plain_circuit()
assert not check_all(n, tabs, g, o, 0), 'plain circuit wrong'
# bit_wires vs lean_wires on random rows
import random
rng = random.Random(5)
W = bit_wires(n, g)
for _ in range(300):
    t = rng.randrange(1 << n)
    x = [bool((t >> i) & 1) for i in range(n)]
    lw = lean_wires(g, x)
    assert all(lw[k] == bool((W[k] >> t) & 1) for k in range(len(lw)))
print('plain 39 ok, evaluator ok')
for s, mn in ((39, 0),):
    r = cegis(n, tabs, LINES, s, maxnot=mn, time_limit=600)
    print(s, mn, r[0], r[3])
    if r[1]: print(r[1])
