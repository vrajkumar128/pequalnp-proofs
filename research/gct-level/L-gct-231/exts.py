import sympy as sp
from itertools import permutations
def perm(M):
    return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(4)]) for p in permutations(range(4))))
x,y=sp.symbols('x y')
b=[0,x,y,-x-y]
t=sp.zeros(4,4)
for j in range(4):
    t[0,j]+=b[j]; t[j,0]+=b[j]
print('perm check:',sp.simplify(perm(sp.ones(4,4)+t)-24))
# extension space: u symmetric with <grad perm(J+t),u>=0 for all x,y
us=sp.symbols('u0:10'); idx=[(i,j) for i in range(4) for j in range(i,4)]
U=sp.zeros(4,4)
for k,(i,j) in enumerate(idx):
    U[i,j]=us[k]; U[j,i]=us[k]
s=sp.symbols('s')
f=sp.expand(perm(sp.ones(4,4)+t+s*U))
lin=sp.Poly(f,s).coeff_monomial(s)
eqs=sp.Poly(lin,x,y).coeffs()
Mx=sp.Matrix([[sp.diff(e,u) for u in us] for e in eqs])
print('rank',Mx.rank(),'ext dim',10-Mx.rank())
ns=Mx.nullspace()
print('nullspace:')
for v in ns: print(list(v))
a=sp.symbols('a0:%d'%len(ns))
uvec=sum((a[k]*ns[k] for k in range(len(ns))),sp.zeros(10,1))
U2=sp.zeros(4,4)
for k,(i,j) in enumerate(idx):
    U2[i,j]=uvec[k]; U2[j,i]=uvec[k]
g=sp.expand(perm(sp.ones(4,4)+t+s*U2)-24)
co=sp.Poly(g,x,y,s).coeffs()
print('conditions:')
for c in set(sp.factor(c) for c in co): print('  ',c)
