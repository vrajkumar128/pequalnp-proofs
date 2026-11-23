import sys, itertools
for line in open(sys.argv[1]):
    n, es = line.split(); n = int(n)
    E = [(int(p[0]), int(p[1])) for p in es.split(',')]
    tau = min(len(T) for r in range(n+1) for T in itertools.combinations(range(n), r) if all(u in T or v in T for u, v in E))
    print(n, es, len(E), tau, len(E) + 2*tau - 2)
