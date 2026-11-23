import sys, time
sys.path.insert(0, '.')
import synth
synth.N = 2
for name, FT in (('x0&~x1', [0,1,0,0]), ('xor', [0,1,1,0])):
    synth.FT = FT
    for s in range(1,6):
        enc = synth.Enc(s, monotone=False)
        for t in range(4): enc.add_row(t)
        enc.add_demorgan_rule()
        r = enc.S.solve()
        if r:
            g = enc.decode(enc.S.get_model()); print(name, s, g, synth.check_all(g)); break
synth.N = 3
synth.FT = [1 if ((t&1) and not (t>>1)&1 and not (t>>2)&1) else 0 for t in range(8)]
for s in range(1,6):
    enc = synth.Enc(s, monotone=False)
    for t in range(8): enc.add_row(t)
    enc.add_demorgan_rule()
    r = enc.S.solve()
    if r:
        g = enc.decode(enc.S.get_model()); print('x0&~x1&~x2', s, g, synth.check_all(g)); break
