import numpy as np, sys
V=np.load(sys.argv[1]); m=V.shape[0]; shp=V.shape[1:]
M=V.reshape(m,-1)
u,s,vh=np.linalg.svd(M,full_matrices=False)
B=vh[:m]  # orthonormal basis of span
# support: entries where some element of L is nonzero
sup=np.linalg.norm(B,axis=0).reshape(shp)
np.set_printoptions(precision=3,suppress=True,linewidth=150)
print('support norms:\n',sup)
