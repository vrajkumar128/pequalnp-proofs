import sys
sys.path.insert(0,'.')
import synth, lns, window
nears = lns.parse_near(sys.argv[1], 19)
for cost, c in nears:
    if cost != 4: continue
    bad = synth.check_all(c)
    cc = window.clean(c)
    print('cost', cost, 'used gates', len(cc), 'nots', sum(1 for g in cc if g[0]=='not'))
    print('  bad rows:', [ (sorted(v for v in range(10) if (t>>v)&1), synth.FT[t]) for t in bad])
