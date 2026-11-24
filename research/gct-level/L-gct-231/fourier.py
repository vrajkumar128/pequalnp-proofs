import sympy as sp, itertools
from itertools import permutations
def perm(M):
    return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(4)]) for p in permutations(range(4))))
I=sp.I
f={k:sp.Matrix([I**(j*k) for j in range(4)]) for k in range(4)}
gens={}
for a in range(1,4):
    for b in range(a,4):
        gens[(a,b)]=sp.expand(f[a]*f[b].T+f[b]*f[a].T)
c=sp.symbols('c0:3')
found=0
for trip in itertools.combinations(gens.keys(),3):
    t=sum((c[k]*gens[trip[k]] for k in range(3)),sp.zeros(4,4))
    g=sp.expand(perm(sp.ones(4,4)+t)-24)
    if g==0:
        print('LEVEL',trip); found+=1
    else:
        nterms=len(sp.Poly(g,*c).coeffs())
        print(trip,'nonzero coeffs',nterms)
print('found',found)
