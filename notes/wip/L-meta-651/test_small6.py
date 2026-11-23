import sys, time
sys.path.insert(0, '.')
import synth
G = [(i,(i+1)%7) for i in range(7)]
synth.set_graph(7, G)
rows = synth.critical_rows()
for variant in ('links', 'plain'):
    enc = synth.Enc(8, monotone=True, solver='cadical195')
    rr = rows + ([0] + [1<<v for v in range(7)] if variant == 'links' else [])
    for t in rr: enc.add_row(t)
    if variant == 'links':
        enc.add_implied_mono(rows); enc.add_mono_links()
    t0=time.time(); r = enc.S.solve(); print(variant, r, round(time.time()-t0,1), flush=True)
