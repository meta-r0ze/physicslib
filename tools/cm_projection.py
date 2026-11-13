#!/usr/bin/env python3
"""Centre-of-mass projection of the three-carrier nucleon on the cube (comparison tool).

Three carriers in the confined ground mode psi (hard-wall cube, ConfinedCarrier). The product
state is projected to zero total momentum by summing lattice translations of the whole system
(cube and carriers together; Peierls-Yoccoz):
  <O>_P = sum_d 3 <psi|o T(d)|psi> N(d)^2 / sum_d N(d)^3,  N(d) = <psi|T(d)|psi>,
for a one-body operator o (spin-flip overlaps vanish, checked). Applied to the axial operator
Sigma_z this gives g_A of the translation-invariant nucleon.

Usage: python3 tools/cm_projection.py [n=3]
"""
import numpy as np, itertools, sys
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
n=int(sys.argv[1]) if len(sys.argv)>1 else 3
Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=n**3; H=np.kron(np.eye(V),H0)-sum(Ns); idx={x:i for i,x in enumerate(sites)}
w,Vv=np.linalg.eigh(H); pos=w>1e-9; e0=w[pos].min(); sub=Vv[:,np.isclose(w,e0,atol=1e-8)]
Sz8=np.kron(np.eye(2),Sz4); Szf=np.kron(np.eye(V),Sz8)
m=sub.conj().T@Szf@sub; ws,vs=np.linalg.eigh((m+m.conj().T)/2); up=sub@vs[:,1]; dn=sub@vs[:,0]
U=up.reshape(V,8); Dn=dn.reshape(V,8)
def shifted_overlap(A,B,d,O=None):
    # sum_x A(x)^dag O B(x-d)
    tot=0j
    for x in sites:
        y=tuple(x[k]-d[k] for k in range(3))
        if y in idx:
            b=B[idx[y]]; tot+=A[idx[x]].conj()@((O@b) if O is not None else b)
    return tot
ds=list(itertools.product(range(-(n-1),n),repeat=3))
Nn=[shifted_overlap(U,U,d) for d in ds]
Nx=[shifted_overlap(U,Dn,d) for d in ds]
Sd=[shifted_overlap(U,U,d,Sz8) for d in ds]
print('max |<up|T(d)|dn>| =',max(abs(x) for x in Nx))
den=sum(N**3 for N in Nn).real
num=sum(S*N**2 for S,N in zip(Sd,Nn)).real
print('n %d: <Sigma_z> unprojected %.4f  projected (zero total momentum, Peierls-Yoccoz) %.4f  ratio %.4f'%(n,Sd[ds.index((0,0,0))].real,num/den,num/den/Sd[ds.index((0,0,0))].real))
print('  g_A = (5/3)<Sigma_z>: %.4f -> %.4f'%(5/3*Sd[ds.index((0,0,0))].real,5/3*num/den))

