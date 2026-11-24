import sys,time
from depthsat import depth_sat
inst=open(sys.argv[1]).read().split('\n')
n=int(inst[0]); a=list(map(int,inst[1].split()))[1:]; b=list(map(int,inst[2].split()))[1:]
D=int(sys.argv[2])
out=open(sys.argv[3]).read().split('\n')
HA=[int(x) for l in out if l.startswith('HARD A:') for x in l.split(':')[1].split()]
HB=[int(x) for l in out if l.startswith('HARD B:') for x in l.split(':')[1].split()]
full=(1<<n)-1
ones=[a[i] for i in HA]; zeros=[full^b[i] for i in HB]
print(len(ones),len(zeros),flush=True)
t=time.time(); r=depth_sat(n,ones,zeros,D,solver=sys.argv[4] if len(sys.argv)>4 else 'cadical153')
print('D=%d'%D,'SAT '+r if r else 'UNSAT','%.1fs'%(time.time()-t),flush=True)
