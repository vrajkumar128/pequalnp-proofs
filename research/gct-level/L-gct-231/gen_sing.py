import sympy as sp, itertools, sys
from itertools import permutations
# H coordinates: 9 coords, t00 eliminated by S1 = 0
names=['t11','t22','t33','t01','t02','t03','t12','t13','t23']
def mat_from_coords(c):
    d=dict(zip(names,c))
    t00=-(d['t11']+d['t22']+d['t33'])-2*(d['t01']+d['t02']+d['t03']+d['t12']+d['t13']+d['t23'])
    full={(0,0):t00,(1,1):d['t11'],(2,2):d['t22'],(3,3):d['t33']}
    for (i,j) in [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]:
        full[(i,j)]=d['t%d%d'%(i,j)]; full[(j,i)]=d['t%d%d'%(i,j)]
    return sp.Matrix(4,4,lambda i,j: full[(i,j)])
def perm(M):
    return sum(sp.prod([M[i,p[i]] for i in range(4)]) for p in permutations(range(4)))
def system(piv, field_note=''):
    nonpiv=[k for k in range(9) if k not in piv]
    X=sp.symbols('x0:%d'%(3*len(nonpiv)))
    cs=sp.symbols('c1:4')
    vecs=[]
    idx=0
    for a in range(3):
        v=[0]*9
        v[piv[a]]=1
        for k in nonpiv:
            v[k]=X[idx]; idx+=1
        vecs.append(v)
    coords=[sum(cs[a]*vecs[a][k] for a in range(3)) for k in range(9)]
    t=mat_from_coords(coords)
    f=sp.expand(perm(sp.ones(4,4)+t)-24)
    P=sp.Poly(f,*cs)
    eqs=[sp.expand(c) for c in P.coeffs()]
    return X,eqs
if __name__=='__main__':
    piv=[int(a) for a in sys.argv[1].split(',')]
    char=sys.argv[2]
    X,eqs=system(piv)
    with open(sys.argv[3],'w') as fh:
        fh.write('ring r=%s,(%s),dp;\n'%(char,','.join(str(x) for x in X)))
        fh.write('ideal I=\n'+',\n'.join(str(e).replace('**','^') for e in eqs)+';\n')
        fh.write('option(redSB);\nideal G=std(I);\nprint(size(G));\nprint(dim(G));\nif(size(G)<5){print(G);}\nquit;\n')
