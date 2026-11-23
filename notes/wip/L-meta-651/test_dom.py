import sys, time
sys.path.insert(0, '.')
import synth
for name, n, G in [('C7', 7, [(i,(i+1)%7) for i in range(7)]), ('C5', 5, [(i,(i+1)%5) for i in range(5)])]:
    synth.set_graph(n, G)
    rows = synth.critical_rows()
    for s in [int(x) for x in sys.argv[1].split(',')]:
        enc = synth.Enc(s, monotone=True, solver='cadical195')
        for t in rows: enc.add_row(t)
        enc.add_dominance(rows)
        t0=time.time(); r = enc.S.solve(); print(name, s, r, round(time.time()-t0,1), flush=True)
        if r:
            g = enc.decode(enc.S.get_model()); print(g, synth.check_all(g))
