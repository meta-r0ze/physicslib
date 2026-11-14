#!/usr/bin/env python3
"""The local axial variation of the two-slice update (PMAction REVIEW, carrier update).

The update H = H0 - sum_j N_j (plain truncation, the selected completion) has a natural local
axial rotation: the slice sign S = diag(1,1,1,1,-1,-1,-1,-1), rotating the two D4 slices
oppositely (the domain-wall axial rotation). Algebra (checked below): S commutes with every hop
block c_j and with the on-site 3 beta; it anticommutes with the inter-slice coupling. So the
axial charge is conserved except for the wall term at the inter-slice coupling, and its link
current is A_j = sym(S v_j), v_j = i[H, x_j], with no adjustable Z_A.

Free carrier (periodic, momentum k along z; run tools/slice_axial.py with no arguments for the
free check only): <sym(S v_z)> = helicity * (1 - O(k^2)), same sign as Sigma_z: the current is
exactly normalized.

Confined carrier (spin-up ground doublet, exact diagonalization):
  n   Sigma_z   |sym(S v_z)|
  3   0.826     0.223
  4   0.759     0.302
  5   0.717     0.358
  6   0.692     0.397
  7   0.677     0.427
  8   0.668     0.449
Sigma_z tends to about 0.65 (the MIT-bag value); the conserved current rises but extrapolates to
about 0.5. With only two slices the wall leakage of the slice-sign rotation is O(1), so this
current neither confirms the on-site operator nor gives a usable g_A ((5/3) 0.22 = 0.37 on 3^3).

Usage: python3 tools/slice_axial.py 3 4 5   (cube sizes; dense, n <= 8)
"""
import numpy as np, contextlib, io
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
with contextlib.redirect_stdout(io.StringIO()): exec(src)
S8=np.diag([1]*4+[-1]*4).astype(complex)
G5=bd(gam)
# algebra: S commutes with every hop block and the on-site 3beta; only inter-slice hop breaks
Hd=np.block([[3*beta,np.zeros((4,4))],[np.zeros((4,4)),3*beta]]); Hx=H0-Hd
print('[S,c_j]=0:',all(np.allclose(S8@cj,cj@S8) for cj in c),' [S,3beta]=0:',np.allclose(S8@Hd,Hd@S8),' {S,interslice}=0:',np.allclose(S8@Hx,-Hx@S8))

# free-carrier normalization
def Hk(k):
    M=H0.copy()
    for j in range(3): M=M-(np.exp(1j*k[j])*c[j]+np.exp(-1j*k[j])*c[j].conj().T)
    return M
def dHk(k,j): return -(1j*np.exp(1j*k[j])*c[j]-1j*np.exp(-1j*k[j])*c[j].conj().T)
for kz in (0.05,0.2,0.5):
    k=[0,0,kz]; w,v=np.linalg.eigh(Hk(k))
    for ii in np.argsort(abs(w))[:2]:
        u=v[:,ii]; vz=dHk(k,2); A=(S8@vz+vz@S8)/2
        print('free kz %.2f E %+.4f <sym(S vz)> %+.4f <Sz> %+.4f'%(kz,w[ii],(u.conj()@A@u).real,(u.conj()@bd(Sz4)@u).real))
for n in tuple(int(a) for a in __import__("sys").argv[1:]):
    Ns=[]
    for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
    V=n**3; H=np.kron(np.eye(V),H0)-sum(Ns)
    Z=np.kron(np.diag([x[2] for x in sites]).astype(float),np.eye(8)); vz=1j*(H@Z-Z@H)
    Sl=np.kron(np.eye(V),S8); Q5=np.kron(np.eye(V),S8@G5); Sz=np.kron(np.eye(2*V),Sz4)
    w,Vv=np.linalg.eigh(H); pos=w>1e-7; e0=w[pos].min(); sel=np.isclose(w,e0,atol=1e-6); sub=Vv[:,sel]
    Sm=sub.conj().T@Sz@sub; ws,vs=np.linalg.eigh((Sm+Sm.conj().T)/2); up=sub@vs[:,-1]
    ex=lambda O:(up.conj()@O@up).real
    Aslice=(Sl@vz+vz@Sl)/2; Ag5=(Q5@vz+vz@Q5)/2; Ag=( np.kron(np.eye(V),G5)@vz+vz@np.kron(np.eye(V),G5))/2
    # Ward check: <[H, S_tot]> = 0 on eigenstate; local: J5q density
    print(n,'Sz %.4f | sym(S vz) %.4f | sym(S g5 vz) %.4f | sym(g5 vz) %.4f'%(ex(Sz),ex(Aslice),ex(Ag5),ex(Ag)),flush=True)
