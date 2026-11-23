import sys, time
sys.path.insert(0,'.')
from probe import probe
from graphs import *
from synth2 import restrict_multi, G as GG
which = sys.argv[1]
if which == 'H':
    E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(3,7),(4,8),(5,9)]; n = 10; u, v = 0, 1
elif which == 'DS2':
    # double star where a is a hub too: u=0,v=1,a=2,b=3,c=4,d=5; a has leaves 6,7
    E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7)]; n = 8; u, v = 0, 1
elif which == 'DS1':
    # u=0,v=1,a=2,b=3,c=4,d=5; a-6 pendant
    E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6)]; n = 7; u, v = 0, 1
elif which == 'G4':
    n, E = GG['G4']; u, v = 0, 6
m = mu(E, ())
need_u = m - mu(*restrict_multi(E, {u:0})); need_v = m - mu(*restrict_multi(E, {v:0}))
print(which, 'n', n, 'mu', m, 'tau', tau(E), 'need u0', need_u, 'need v0', need_v, flush=True)
probe(n, E, m, [({u:0},3), ({v:0},3)])
