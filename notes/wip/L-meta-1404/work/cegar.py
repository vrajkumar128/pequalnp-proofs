import sys, random, time, re
from depthsat import depth_sat, mono_rows, maj
from fdef import MIN, MAX
n=15; D=int(sys.argv[1]); seed=int(sys.argv[2]); random.seed(seed)
ones=[sum(1<<i for i in m) for m in MIN]
zeros=[((1<<15)-1)^sum(1<<i for i in m) for m in MAX]
def evalf(s, t):
    env={'x%d'%i: bool(t>>i&1) for i in range(n)}
    return eval(s.replace('&',' and ').replace('|',' or '), {}, env)
R1=random.sample(ones,4); R0=random.sample(zeros,4)
it=0
while True:
    it+=1; t=time.time()
    r=depth_sat(n,R1,R0,D)
    print('iter',it,len(R1),len(R0),'SAT' if r else 'UNSAT','%.1fs'%(time.time()-t),flush=True)
    if not r:
        print('R1',R1); print('R0',R0); break
    bad1=[x for x in ones if not evalf(r,x)]; bad0=[x for x in zeros if evalf(r,x)]
    if not bad1 and not bad0:
        print('FOUND',r); break
    if bad1: R1.append(random.choice(bad1))
    if bad0: R0.append(random.choice(bad0))
