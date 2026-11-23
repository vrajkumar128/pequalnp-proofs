import itertools, sys
def wires(n, gates, x):
    w = list(x)
    for op, ins in gates:
        vals = [w[i] if i < len(w) else False for i in ins]
        w.append(all(vals) if op == 'and' else any(vals))
    return w
def getD(l, i): return l[i] if i < len(l) else False
def analyse(n, gates, out, E):
    unit = [wires(n, gates, [i == u for i in range(n)]) for u in range(n)]
    pair = {}
    for u in range(n):
        for v in range(u+1, n):
            pair[(u, v)] = wires(n, gates, [i in (u, v) for i in range(n)])
    def fat(w): return sum(getD(unit[u], w) for u in range(n)) >= 2
    full_ok = all(getD(wires(n, gates, list(x)), out) == any(x[u] and x[v] for (u, v) in E)
                  for x in itertools.product([False, True], repeat=n))
    pair_ok = all(not getD(unit[u], out) for u in range(n)) and all(getD(pair[p], out) == (p in E) for p in pair)
    A = sum(1 for op, _ in gates if op == 'and')
    B = sum(1 for j, (op, _) in enumerate(gates) if op == 'or' and fat(n + j))
    D = sum(1 for j, (op, _) in enumerate(gates) if op == 'or' and not fat(n + j))
    des = {}
    for j, (op, ins) in enumerate(gates):
        if op == 'and' and not all(fat(i) for i in ins):
            des[j] = next(i for i in ins if not fat(i))
    reach, stack = {out}, [out]
    while stack:
        r = stack.pop(); j = r - n
        if 0 <= j < len(gates):
            op, ins = gates[j]
            nxt = []
            if op == 'or' and not fat(r): nxt = ins
            if op == 'and' and j in des: nxt = [des[j]]
            for t in nxt:
                if t not in reach: reach.add(t); stack.append(t)
    Fz = 0
    for j, (op, ins) in enumerate(gates):
        if op == 'and' and all(fat(i) for i in ins) and (n + j) in reach:
            acc = [p for p in E if getD(pair[p], n + j)]
            if all(any(c not in p for p in acc) for c in range(n)): Fz += 1
    m = len(E)
    tau = min(len(T) for r in range(n + 1) for T in itertools.combinations(range(n), r)
              if all(u in T or v in T for (u, v) in E))
    print('full_ok', full_ok, 'pair_ok', pair_ok, 'A', A, 'B', B, 'D', D, 'Fz', Fz,
          'LHS |E|+2tau =', m + 2 * tau, 'RHS A+B+2D+Fz+2 =', A + B + 2 * D + Fz + 2)
n = 6
E = {(0, 1), (0, 2), (0, 4), (2, 3), (2, 4), (4, 5)}
g = [('or', [1, 2]), ('or', [6, 4]), ('or', [0, 3]), ('or', [8, 4]), ('or', [0, 2]), ('or', [10, 5]),
     ('and', [7, 9]), ('and', [12, 11])]
print('3-CNF (x1+x2+x4)(x0+x3+x4)(x0+x2+x5):'); analyse(n, g, 6 + len(g) - 1, E)
g2 = [('or', [0, 3]), ('or', [6, 4]), ('or', [0, 2]), ('or', [8, 5]), ('and', [0, 1]), ('or', [2, 4]),
      ('or', [11, 10]), ('and', [9, 12]), ('and', [7, 13])]
print('net circuit of attempt 1:'); analyse(n, g2, 6 + len(g2) - 1, E)
