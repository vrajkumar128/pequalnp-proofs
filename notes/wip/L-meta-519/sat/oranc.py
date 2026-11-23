import sys, time
sys.path.insert(0,'.')
from synth2 import *
from pysat.card import CardEnc, EncType

def add_oranc(enc):
    n, s = enc.n, enc.s; S = enc.S
    last = n + s - 1
    R = {}; Q = {}
    for i in enc.gates: R[i] = enc.new()
    S.add_clause([R[last]])
    for i in enc.gates:
        if i == last: continue
        # R[i] <-> OR_{i2>i} (R[i2] & OR(i2) & uses(i2,i))
        terms = []
        for i2 in range(i+1, n+s):
            t = enc.new()
            u = enc.new()
            S.add_clause([-u, enc.A[i2][i], enc.B[i2][i]]); S.add_clause([u, -enc.A[i2][i]]); S.add_clause([u, -enc.B[i2][i]])
            S.add_clause([-t, R[i2]]); S.add_clause([-t, enc.T[i2][OR]]); S.add_clause([-t, u])
            S.add_clause([t, -R[i2], -enc.T[i2][OR], -u])
            terms.append(t)
        S.add_clause([-R[i]] + terms)
        for t in terms: S.add_clause([R[i], -t])
    for i in enc.gates:
        q = enc.new()
        S.add_clause([-q, R[i]]); S.add_clause([-q, enc.T[i][OR]]); S.add_clause([q, -R[i], -enc.T[i][OR]])
        Q[i] = q
    return [Q[i] for i in enc.gates]

def oranc_of(n, circ):
    s = len(circ); last = n + s - 1
    reach = {last}
    for idx in range(s-1, -1, -1):
        i = n + idx
        if i in reach and circ[idx][0] == 'or':
            for j in circ[idx][1]: reach.add(j)
    return sum(1 for idx in range(s) if (n+idx) in reach and circ[idx][0] == 'or')

def build(n, E, s, extra=(), elim=2, dead=True, allow_not=True):
    def f(r): return any(((r>>u)&1) and ((r>>v)&1) for u,v in E)
    enc = Enc(n, s, allow_not=allow_not); enc.dead = dead
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
    return enc, f

def max_oranc(n, E, s):
    enc, f = build(n, E, s)
    Q = add_oranc(enc)
    best = -1; bestc = None
    k = 0
    while True:
        cl = CardEnc.atleast(lits=Q, bound=k, top_id=enc.nv, encoding=EncType.seqcounter)
        enc.nv = max(enc.nv, cl.nv)
        ok = enc.S.solve(assumptions=[]) if k == 0 else None
        # use a fresh selector for incremental bound
        sel = enc.new()
        for c in cl.clauses: enc.S.add_clause(c + [-sel])
        if not enc.S.solve(assumptions=[sel]): break
        c = enc.extract(enc.S.get_model())
        best = oranc_of(n, c); bestc = c
        k = best + 1
    return best, bestc

if __name__ == '__main__':
    which = sys.argv[1]
    if which == 'DS1':
        E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6)]; n = 7; u, v = 0, 1
    elif which == 'DS':
        E = [(0,1),(0,2),(0,3),(1,4),(1,5)]; n = 6; u, v = 0, 1
    elif which == 'DS2':
        E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7)]; n = 8; u, v = 0, 1
    elif which == 'DS3':
        # both a and c have pendants: u=0,v=1,a=2,b=3,c=4,d=5, a-6, c-7
        E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(4,7)]; n = 8; u, v = 0, 1
    elif which == 'DS3b':
        E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(3,7)]; n = 8; u, v = 0, 1
    elif which == 'G4':
        n, E = G['G4']; u, v = 0, 6
    elif which == 'H':
        E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(3,7),(4,8),(5,9)]; n = 10; u, v = 0, 1
    elif which == 'DS4':
        # all of a,b,c,d have pendants
        E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(3,7),(4,8),(5,9)]; n = 10; u, v = 0, 1
    m = mu(E, ())
    t0 = time.time()
    M, c = max_oranc(n, E, m)
    print(which, 'mu', m, 'max orAnc among least circuits', M, c, round(time.time()-t0,1), flush=True)
    enc, f = build(n, E, m, extra=[({u:0},3), ({v:0},3)])
    Q = add_oranc(enc)
    cl = CardEnc.atleast(lits=Q, bound=M, top_id=enc.nv, encoding=EncType.seqcounter)
    for c2 in cl.clauses: enc.S.add_clause(c2)
    enc.nv = max(enc.nv, cl.nv)
    if enc.S.solve():
        c = enc.extract(enc.S.get_model())
        print('L2 FAILS in an orAnc-max least circuit:', c, 'orAnc', oranc_of(n, c), round(time.time()-t0,1))
    else:
        print('L2 holds for all orAnc-max least circuits', round(time.time()-t0,1))
