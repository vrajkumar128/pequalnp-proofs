import sys, time
sys.path.insert(0, '.')
import synth
def mins(n, edges, mono, smax=12):
    synth.set_graph(n, edges)
    rows = synth.critical_rows()
    for s in range(1, smax+1):
        t0=time.time()
        g = synth.run(s, None, mono, 'cadical195', rows, None, log=lambda m: None)
        if g is not None:
            return s, g, time.time()-t0
C5 = [(0,1),(1,2),(2,3),(3,4),(4,0)]
P4 = [(0,1),(1,2),(2,3)]
for name, n, E in [('P4',4,P4),('C5',5,C5),('2K2',4,[(0,1),(2,3)])]:
    for mono in (True, False):
        print(name, 'mono' if mono else 'demorgan', mins(n,E,mono), flush=True)
