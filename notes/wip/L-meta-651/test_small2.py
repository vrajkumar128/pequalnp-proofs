import sys, time
sys.path.insert(0, '.')
import synth
C5 = [(0,1),(1,2),(2,3),(3,4),(4,0)]
synth.set_graph(5, C5)
rows = synth.critical_rows()
for s in (6,7):
    enc = synth.Enc(s, monotone=True)
    for t in rows: enc.add_row(t)
    enc.add_implied_mono(rows)
    t0=time.time(); r = enc.S.solve(); print(s, r, time.time()-t0)
    if r: print(enc.decode(enc.S.get_model()), synth.check_all(enc.decode(enc.S.get_model())))
