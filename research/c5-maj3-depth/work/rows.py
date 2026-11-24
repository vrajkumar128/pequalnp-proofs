import itertools
N=15
def maj(a,b,c): return (a&b)|(a&c)|(b&c)
def F(t):
    z=[(t>>i)&1 for i in range(N)]
    m=[maj(z[v],z[v+5],z[v+10]) for v in range(5)]
    return int(any(m[v] and m[(v+1)%5] for v in range(5)))
def blk(v): return [v,v+5,v+10]
def minterms():
    res=[]
    for i in range(5):
        j=(i+1)%5
        for p in itertools.combinations(blk(i),2):
            for q in itertools.combinations(blk(j),2):
                res.append(sum(1<<x for x in p+q))
    return res
def maxfalse():
    res=[]
    for j in range(5):
        ind={j,(j+2)%5}
        others=[v for v in range(5) if v not in ind]
        base=sum(1<<x for v in ind for x in blk(v))
        for qs in itertools.product(*[blk(v) for v in others]):
            res.append(base+sum(1<<x for x in qs))
    return res
A=minterms(); B=maxfalse()
if __name__=='__main__':
    tt=[F(t) for t in range(1<<N)]
    mins=sorted(t for t in range(1<<N) if tt[t] and all(not tt[t&~(1<<i)] for i in range(N) if t>>i&1))
    maxf=sorted(t for t in range(1<<N) if not tt[t] and all(tt[t|(1<<i)] for i in range(N) if not t>>i&1))
    print(len(A),len(set(A)),len(B),len(set(B)))
    print('minterms ok',mins==sorted(A),'maxfalse ok',maxf==sorted(B))
    # also check f matches Lean statement formula
    def lean(t):
        z=[(t>>i)&1 for i in range(N)]
        M=lambda a,b,c:(z[a]&z[b])|(z[a]&z[c])|(z[b]&z[c])
        m=[M(v,v+5,v+10) for v in range(5)]
        return (m[0]&m[1])|(m[1]&m[2])|(m[2]&m[3])|(m[3]&m[4])|(m[4]&m[0])
    print('lean formula matches', all(lean(t)==tt[t] for t in range(1<<N)))
