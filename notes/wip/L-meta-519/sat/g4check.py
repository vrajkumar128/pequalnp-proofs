import sys
sys.path.insert(0,'.')
from graphs import *
def cyc_leaves(m, hubs):
    E = [(i,(i+1)%m) for i in range(m)]
    for t,h in enumerate(hubs): E.append((h, m+t))
    return (m+len(hubs), E)
n, E = cyc_leaves(7, [0,3,6])
print('tau', tau(E), 'mu', mu(E, ()), 'girth', girth(E), 'in522', in522(E), 'provable', provable(E))
for v in range(n):
    for b in (0,1):
        E2, A2 = restrict(E, v, b)
        print(v, b, 'mu', mu(E2, A2), 'need', mu(E,())-mu(E2,A2), 'provable', provable(E2, A2))
