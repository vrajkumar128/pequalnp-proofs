import sympy as sp
def perm(M):
    from itertools import permutations
    return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(4)]) for p in permutations(range(4))))
J=sp.ones(4,4)
al,be=sp.symbols('alpha beta')
v=sp.symbols('v0:3'); vv=list(v)+[-sum(v)]
t=sp.zeros(4,4)
for i in range(4):
    for j in range(4):
        t[i,j]= al*vv[i] if i==j else be*(vv[i]+vv[j])
P=sp.Poly(perm(J+t)-24,*v)
print('V-copy coefficients:')
cs=[sp.factor(c) for c in P.coeffs()]
print(set(cs))
print(sp.solve(cs,[al,be],dict=True))
s,x,y=sp.symbols('s x y'); z=-x-y
f={frozenset({0,1}):x,frozenset({2,3}):x,frozenset({0,2}):y,frozenset({1,3}):y,frozenset({0,3}):z,frozenset({1,2}):z}
t2=sp.zeros(4,4)
for i in range(4):
    for j in range(4):
        t2[i,j]= s*3 if i==j else -s + f[frozenset({i,j})]
print('1+U2:', sp.factor(perm(J+t2)-24))
