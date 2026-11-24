import numpy as np, time
from fast4 import *
rng=np.random.default_rng(0)
pp=PermPQ(5,5); amb=ambient(5,5)
pr=Problem(pp,amb,7,rng)
X=rng.normal(size=(pr.N2-7,7))+0j
print('nsamp',pr.C.shape)
t=time.time()
for _ in range(10): pr.res_jac(X)
print('res_jac',(time.time()-t)/10)
t=time.time()
for _ in range(10): pr.res_jac(X,need_jac=False)
print('res only',(time.time()-t)/10)
A=pr.B+np.zeros((pr.C.shape[0],5,5))
t=time.time()
for _ in range(10): pp.val_grad(A)
print('val_grad',(time.time()-t)/10)
r,J=pr.res_jac(X)
t=time.time()
for _ in range(10): JH=J.conj().T; Am=JH@J
print('JHJ',(time.time()-t)/10, J.shape)
import os; print(os.cpu_count())
