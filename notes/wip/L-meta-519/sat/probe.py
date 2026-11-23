import sys, time
sys.path.insert(0,'.')
from synth2 import *
def probe(n, E, s, extra, elim=2, allow_not=True, dead=True):
    def f(r): return any(((r>>u)&1) and ((r>>v)&1) for u,v in E)
    enc = Enc(n, s, allow_not=allow_not)
    enc.dead = dead
    assigns = [{v:b} for v in range(n) for b in (0,1)]
    if elim >= 2:
        assigns += [{v:b, w:c} for v in range(n) for w in range(v+1, n) for b in (0,1) for c in (0,1)]
    for a in assigns:
        rr = restrict_multi(E, a)
        if rr is None: continue
        E2, A2 = rr
        if not (E2 or A2): continue
        if provable(E2, A2): enc.add_elim(a, s - mu(E2, A2))
    for a, t in extra: enc.add_elim(a, t)
    for r in range(1<<n): enc.add_row(r, f(r))
    t0=time.time()
    if enc.S.solve():
        c = enc.extract(enc.S.get_model())
        assert all(evalc(n,c,r)==f(r) for r in range(1<<n))
        print('SAT', round(time.time()-t0,1), c); return c
    print('UNSAT', round(time.time()-t0,1)); return None
if __name__ == '__main__':
    E = [(0,1),(0,2),(0,3),(1,4),(1,5)]
    print('double star, dead counting: both hubs <=3')
    probe(6, E, 6, [({0:0},3), ({1:0},3)])
    # longer: u=0,v=1; u-a(2)-a'(6), u-b(3)-b'(7); v-c(4)-c'(8), v-d(5)-d'(9)
    E2 = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(3,7),(4,8),(5,9)]
    m2 = mu(E2,())
    print('spider-H mu', m2, 'tau', tau(E2), 'needs u0', m2-mu(*restrict_multi(E2,{0:0})), 'v0', m2-mu(*restrict_multi(E2,{1:0})))
    probe(10, E2, m2, [({0:0},3), ({1:0},3)])
