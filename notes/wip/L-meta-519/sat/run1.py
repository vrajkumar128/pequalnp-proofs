import sys, time
sys.path.insert(0, '.')
from synth import *
name = sys.argv[1]; s = int(sys.argv[2])
G = {
 'C7': (7, [(i,(i+1)%7) for i in range(7)]),
 'C8': (8, [(i,(i+1)%8) for i in range(8)]),
 'G1': (9, [(i,(i+1)%7) for i in range(7)] + [(0,7),(3,8)]),
 'G2': (10, [(i,(i+1)%7) for i in range(7)] + [(0,7),(2,8),(4,9)]),
 'G3': (10, [(i,(i+1)%8) for i in range(8)] + [(0,8),(4,9)]),
}
n,E = G[name]
f = edge_fn(n,E)
t=time.time()
c = synth(n, s, f, init_rows_for(n,E), verbose=True)
print(name, s, c, time.time()-t)
