import sys, time
sys.path.insert(0, '.')
import synth
rows = synth.critical_rows()
mono = sys.argv[1] == 'mono'
for s in [int(x) for x in sys.argv[2].split(',')]:
    enc = synth.Enc(s, monotone=mono, solver='cadical195', shard=4)
    for t in rows: enc.add_row(t)
    if mono: enc.add_implied_mono(rows)
    t0=time.time(); r = enc.S.solve(); print(s, 'mono' if mono else 'dm', r, round(time.time()-t0,1), flush=True)
    if r:
        g = enc.decode(enc.S.get_model()); print(g, len(synth.check_all(g)), flush=True)
