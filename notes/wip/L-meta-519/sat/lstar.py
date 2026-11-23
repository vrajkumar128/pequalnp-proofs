import sys, time
sys.path.insert(0,'.')
from oranc import *
from graphs import adj

def test_lstar(name, n, E, use_max=True, elim=2, s_override=None):
    m = mu(E, ()) if s_override is None else s_override
    t0 = time.time()
    if use_max:
        M, c = max_oranc(n, E, m)
    else:
        M = 0
    A = adj(E)
    extra = []
    for u in range(n):
        if u not in A: continue
        E2 = [e for e in E if u not in e]
        if not E2: continue
        extra.append(({u:0}, len(A[u])))
    enc, f = build(n, E, m, extra=extra, elim=elim)
    Q = add_oranc(enc)
    if M > 0:
        cl = CardEnc.atleast(lits=Q, bound=M, top_id=enc.nv, encoding=EncType.seqcounter)
        for c2 in cl.clauses: enc.S.add_clause(c2)
        enc.nv = max(enc.nv, cl.nv)
    if enc.S.solve():
        c = enc.extract(enc.S.get_model())
        print(name, 'mu', m, 'maxOrAnc', M, 'L* FAILS:', c, 'orAnc', oranc_of(n, c), round(time.time()-t0,1), flush=True)
    else:
        print(name, 'mu', m, 'maxOrAnc', M, 'L* holds', round(time.time()-t0,1), flush=True)

if __name__ == '__main__':
    tests = {
      'P4': (4, [(0,1),(1,2),(2,3)]),
      'P5': (5, [(0,1),(1,2),(2,3),(3,4)]),
      'DS': (6, [(0,1),(0,2),(0,3),(1,4),(1,5)]),
      'C5': (5, [(i,(i+1)%5) for i in range(5)]),
      'C6': (6, [(i,(i+1)%6) for i in range(6)]),
      'DS1': (7, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6)]),
      'C7': (7, [(i,(i+1)%7) for i in range(7)]),
    }
    tests['C7L1'] = cyc_leaves(7, [0])
    tests['DS2'] = (8, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7)])
    tests['DS3'] = (8, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(4,7)])
    tests['H'] = (10, [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(3,7),(4,8),(5,9)])
    tests['G4'] = G['G4']
    tests['T344'] = G['T344']
    for k in sys.argv[1:]:
        if k == 'C4':
            test_lstar('C4@3', 4, [(0,1),(1,2),(2,3),(3,0)], s_override=3); continue
        n, E = tests[k]
        test_lstar(k, n, E)
