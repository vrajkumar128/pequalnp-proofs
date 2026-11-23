import sys, time
sys.path.insert(0, '.')
from synth import *
def cyc_leaves(m, hubs):
    E = [(i,(i+1)%m) for i in range(m)]
    for t,h in enumerate(hubs): E.append((h, m+t))
    return (m+len(hubs), E)
G = {
 'C7': (7, [(i,(i+1)%7) for i in range(7)]),
 'G4': cyc_leaves(7, [0,3,6]),
 'G5': cyc_leaves(7, [0,1,2,3,4]),
 'S7': cyc_leaves(7, list(range(7))),
}
name = sys.argv[1]; s = int(sys.argv[2]); mono = sys.argv[3] == 'mono'
n,E = G[name]
f = edge_fn(n,E)
t=time.time()
c = synth(n, s, f, init_rows_for(n,E), verbose=True, allow_not=not mono, every=5)
print(name, s, 'mono' if mono else 'full', c, time.time()-t, flush=True)
