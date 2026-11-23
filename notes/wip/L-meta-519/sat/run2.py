import sys, time
sys.path.insert(0, '.')
from synth import *
def cyc_leaves(m, hubs):
    E = [(i,(i+1)%m) for i in range(m)]
    for t,h in enumerate(hubs): E.append((h, m+t))
    return (m+len(hubs), E)
G = {
 'G4': cyc_leaves(7, [0,3,6]),
 'G5': cyc_leaves(7, [0,1,2,3,4]),
 'S7': cyc_leaves(7, list(range(7))),
}
name = sys.argv[1]; s = int(sys.argv[2])
n,E = G[name]
f = edge_fn(n,E)
t=time.time()
c = synth(n, s, f, init_rows_for(n,E), verbose=True)
print(name, s, c, time.time()-t, flush=True)
