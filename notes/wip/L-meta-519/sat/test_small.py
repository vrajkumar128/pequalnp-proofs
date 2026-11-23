import sys
sys.path.insert(0, '.')
from synth import *
tests = {
 'C4': (4, [(0,1),(1,2),(2,3),(3,0)]),
 'P4': (4, [(0,1),(1,2),(2,3)]),
 'C5': (5, [(i,(i+1)%5) for i in range(5)]),
 'C6': (6, [(i,(i+1)%6) for i in range(6)]),
}
for name,(n,E) in tests.items():
    f = edge_fn(n,E)
    for s in range(1, 12):
        c = synth(n, s, f, init_rows_for(n,E), verbose=False)
        if c is not None:
            print(name, 'min size', s, c, flush=True); break
