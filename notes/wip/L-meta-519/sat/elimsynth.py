import sys, time, random
sys.path.insert(0, '.')
from synth import Synth, evalc, edge_fn, init_rows_for
from graphs import *
from pysat.card import CardEnc, EncType

def add_elim_constraints(sy, v, b, maxkill):
    n, s = sy.n, sy.s
    K, C = {}, {}
    for i in range(n, n+s):
        K[i] = sy.new(); C[(i,0)] = sy.new(); C[(i,1)] = sy.new()
    def const_lit(w, c):
        # returns True (always const c), False (never), or var
        if w == v: return (b == c)
        if w < n: return False
        return C[(w,c)]
    for i in range(n, n+s):
        for (sv, op, ins) in sy.sel[i]:
            # killed
            for w in ins:
                for c in (0,1):
                    l = const_lit(w, c)
                    if l is True: sy.S.add_clause([-sv, K[i]])
                    elif l is not False: sy.S.add_clause([-sv, -l, K[i]])
            if op == 'not':
                for c in (0,1):
                    l = const_lit(ins[0], c)
                    if l is True: sy.S.add_clause([-sv, C[(i,1-c)]])
                    elif l is not False: sy.S.add_clause([-sv, -l, C[(i,1-c)]])
            else:
                dom = 0 if op == 'and' else 1   # dominating constant
                for w in ins:
                    l = const_lit(w, dom)
                    if l is True: sy.S.add_clause([-sv, C[(i,dom)]])
                    elif l is not False: sy.S.add_clause([-sv, -l, C[(i,dom)]])
                nd = 1 - dom
                l1 = const_lit(ins[0], nd); l2 = const_lit(ins[1], nd)
                if l1 is not False and l2 is not False:
                    cl = [-sv, C[(i,nd)]]
                    for l in (l1, l2):
                        if l is not True: cl.append(-l)
                    sy.S.add_clause(cl)
    lits = [K[i] for i in range(n, n+s)]
    if maxkill < 0:
        sy.S.add_clause([]); return
    enc = CardEnc.atmost(lits=lits, bound=maxkill, top_id=sy.nv, encoding=EncType.seqcounter)
    for cl in enc.clauses: sy.S.add_clause(cl)
    sy.nv = max(sy.nv, enc.nv)

def run(n, E, s, allow_not=True, verbose=True, seed=0):
    random.seed(seed)
    f = edge_fn(n, E)
    m0 = mu(E, ())
    sy = Synth(n, s, f, allow_not=allow_not)
    cons = 0
    for v in range(n):
        for b in (0,1):
            E2, A2 = restrict(E, v, b)
            if not (E2 or A2): continue
            if provable(E2, A2):
                lb = mu(E2, A2)
                add_elim_constraints(sy, v, b, s - lb)
                cons += 1
    if verbose: print('n', n, 'mu', m0, 's', s, 'elim constraints', cons, 'vars', sy.nv, flush=True)
    for r in init_rows_for(n, E): sy.add_row(r)
    it = 0; t0 = time.time()
    while True:
        it += 1
        ok = sy.S.solve()
        if not ok:
            print(f'UNSAT after {it} iters, {len(sy.rows)} rows, {time.time()-t0:.1f}s', flush=True)
            return None
        circ = sy.extract(sy.S.get_model())
        bad = [r for r in range(1<<n) if evalc(n, circ, r) != f(r)]
        if not bad:
            print(f'SAT after {it} iters, {len(sy.rows)} rows, {time.time()-t0:.1f}s', flush=True)
            print(circ, flush=True)
            return circ
        random.shuffle(bad)
        for r in bad[:2]: sy.add_row(r)
        if verbose and it % 5 == 0: print(f' iter {it} rows {len(sy.rows)} t {time.time()-t0:.1f}', flush=True)

def cyc_leaves(m, hubs):
    E = [(i,(i+1)%m) for i in range(m)]
    for t,h in enumerate(hubs): E.append((h, m+t))
    return (m+len(hubs), E)

if __name__ == '__main__':
    which = sys.argv[1]; s = int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'full'
    G = {
      'C5': (5, [(i,(i+1)%5) for i in range(5)]),
      'C7': (7, [(i,(i+1)%7) for i in range(7)]),
      'P5': (5, [(0,1),(1,2),(2,3),(3,4)]),
      'G4': cyc_leaves(7, [0,3,6]),
      'G5': cyc_leaves(7, [0,1,2,3,4]),
      'C8L': cyc_leaves(8, [0,3,6,7]),
      'C9L': cyc_leaves(9, [0,3,6]),
      'S7': cyc_leaves(7, list(range(7))),
    }
    n, E = G[which]
    run(n, E, s, allow_not=(mode=='full'))
