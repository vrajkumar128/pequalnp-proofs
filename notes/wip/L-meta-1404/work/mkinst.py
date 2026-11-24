import sys
from depthsat import mono_rows, maj
def inst(n,f):
    mins,maxf=mono_rows(n,f)
    full=(1<<n)-1
    zs=[full^t for t in maxf]
    return '%d\n%d %s\n%d %s\n'%(n,len(mins),' '.join(map(str,mins)),len(zs),' '.join(map(str,zs)))
fs={
 'maj': (3,lambda z:maj(*z)),
 'c5': (5,lambda m:any(m[v] and m[(v+1)%5] for v in range(5))),
 'G': (9,lambda z:maj(*z[:3]) and (maj(*z[3:6]) or maj(*z[6:]))),
 'p4': (12,lambda z:(maj(*z[0:3]) and maj(*z[3:6])) or (maj(*z[3:6]) and maj(*z[6:9])) or (maj(*z[6:9]) and maj(*z[9:12]))),
 'F': (15,lambda z:any(maj(z[v],z[v+5],z[v+10]) and maj(z[(v+1)%5],z[(v+1)%5+5],z[(v+1)%5+10]) for v in range(5))),
}
n,f=fs[sys.argv[1]]
open(sys.argv[1]+'.inst','w').write(inst(n,f))
