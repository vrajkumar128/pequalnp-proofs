import sympy as sp, random, sys
from itertools import permutations
from gen_sing import mat_from_coords, perm
random.seed(int(sys.argv[1]))
# random integer change of coordinates on H (9-dim): coords = M * y
while True:
    M=sp.Matrix(9,9,lambda i,j: random.randint(-3,3))
    if M.det()!=0: break
X=sp.symbols('x0:18'); cs=sp.symbols('c1:4')
vecs=[]
idx=0
for a in range(3):
    y=[0]*9; y[a]=1
    for k in range(3,9):
        y[k]=X[idx]; idx+=1
    vecs.append(M*sp.Matrix(y))
coords=[sum(cs[a]*vecs[a][k] for a in range(3)) for k in range(9)]
t=mat_from_coords(coords)
f=sp.expand(perm(sp.ones(4,4)+t)-24)
P=sp.Poly(f,*cs)
eqs=[sp.expand(c) for c in P.coeffs()]
with open(sys.argv[2],'w') as fh:
    fh.write('ring r=%s,(%s),dp;\n'%(sys.argv[3],','.join(str(x) for x in X)))
    fh.write('ideal I=\n'+',\n'.join(str(e).replace('**','^') for e in eqs)+';\n')
    fh.write('ideal G=slimgb(I);\nprint(size(G));\nprint(dim(G));\nif(size(G)<5){print(G);}\nquit;\n')
print(len(eqs))
