import itertools
def simplify(n, circ, assign):
    # wires: ('c', bool) constant, ('w', idx) wire; returns number of gates remaining after const/alias/dead elimination
    rep = {}
    for j in range(n):
        rep[j] = ('c', bool(assign[j])) if j in assign else ('w', j)
    kept = []  # gate idx kept with (op, mapped inputs)
    for idx, (op, ins) in enumerate(circ):
        i = n + idx
        m = [rep[j] for j in ins]
        if op == 'not':
            a = m[0]
            if a[0] == 'c': rep[i] = ('c', not a[1])
            else: rep[i] = ('w', i); kept.append((i, op, m))
        else:
            a, b = m
            dom = False if op == 'and' else True
            if (a[0] == 'c' and a[1] == dom) or (b[0] == 'c' and b[1] == dom): rep[i] = ('c', dom)
            elif a[0] == 'c': rep[i] = b
            elif b[0] == 'c': rep[i] = a
            elif a == b: rep[i] = a
            else: rep[i] = ('w', i); kept.append((i, op, m))
    out = rep[n + len(circ) - 1]
    # dead removal
    live = set()
    if out[0] == 'w': live.add(out[1])
    for (i, op, m) in reversed(kept):
        if i in live:
            for t in m:
                if t[0] == 'w': live.add(t[1])
    remaining = [k for k in kept if k[0] in live]
    return len(circ) - len(remaining), remaining, out

def evalc(n, circ, r):
    vals = [bool((r>>j)&1) for j in range(n)]
    for op, ins in circ:
        if op == 'not': vals.append(not vals[ins[0]])
        elif op == 'and': vals.append(vals[ins[0]] and vals[ins[1]])
        else: vals.append(vals[ins[0]] or vals[ins[1]])
    return vals[-1]

if __name__ == '__main__':
    n = 7
    E = [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6)]
    f = lambda r: any(((r>>u)&1) and ((r>>v)&1) for u,v in E)
    circ = [('or', (2, 3)), ('and', (2, 6)), ('or', (0, 8)), ('or', (5, 9)), ('and', (7, 9)), ('or', (4, 10)), ('or', (1, 11)), ('and', (12, 13))]
    print('correct:', all(evalc(n, circ, r) == f(r) for r in range(1<<n)), 'size', len(circ))
    deg = {}
    for u,v in E: deg[u]=deg.get(u,0)+1; deg[v]=deg.get(v,0)+1
    for u in range(n):
        k, rem, out = simplify(n, circ, {u: 0})
        print('vertex', u, 'deg', deg[u], 'x=0 removes', k)
