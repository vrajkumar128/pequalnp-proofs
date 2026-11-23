import sys, time
sys.path.insert(0, '.')
import synth
G = [(i,(i+1)%7) for i in range(7)]
synth.set_graph(7, G)
rows = synth.critical_rows()
print(len(rows))
for imp in (True, False):
    for s in (8,):
        enc = synth.Enc(s, monotone=True, solver='cadical195')
        for t in rows: enc.add_row(t)
        if imp: enc.add_implied_mono(rows)
        t0=time.time(); r = enc.S.solve(); print('imp', imp, s, r, time.time()-t0, flush=True)
