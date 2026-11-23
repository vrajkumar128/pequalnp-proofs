import sys, time
sys.path.insert(0, '.')
import synth
C5 = [(0,1),(1,2),(2,3),(3,4),(4,0)]
synth.set_graph(5, C5)
for s in (6,7):
    for lim in (None, (1,1)):
        enc = synth.Enc(s, monotone=False)
        for t in range(32): enc.add_row(t)
        enc.add_demorgan_rule()
        if lim: enc.limit_nots(*lim)
        t0=time.time(); r = enc.S.solve(); print(s, lim, r, round(time.time()-t0,2))
        if r:
            g = enc.decode(enc.S.get_model()); print(g, synth.check_all(g))
# a function needing NOT: x0 and not x1 etc: test xor-free: f = x0 & ~x1 on 2 vars via graph module hack
