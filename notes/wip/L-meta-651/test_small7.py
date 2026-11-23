import sys, time
sys.path.insert(0, '.')
import synth
G = [(i,(i+1)%7) for i in range(7)]
synth.set_graph(7, G)
rows = synth.critical_rows()
for s in (8, 9):
  for shard in (4, None):
    enc = synth.Enc(s, monotone=True, solver='cadical195', shard=shard)
    for t in rows: enc.add_row(t)
    t0=time.time(); r = enc.S.solve(); print(s, shard, r, round(time.time()-t0,1), flush=True)
