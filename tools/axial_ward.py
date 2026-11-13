#!/usr/bin/env python3
"""Normalizing the walk's axial current (comparison tool).

1. Which charge is the walk's axial symmetry: on the periodic free walk, |[H(k), Q]|/|H| for
   gamma5 per slice, the slice sign, and their product. The product (slice sign x gamma5)
   commutes with H at k = 0 and nearly so at small k: the chiral symmetry of the zero mode.
2. Free-carrier matching (the lattice analogue of fixing Z_A by an on-shell Ward identity): a
   massless carrier with momentum k along z has continuum axial matrix element <A^z> = helicity =
   1. Compare the on-site Sigma_z and the link current sym(gamma5 v_z), v_z = dH/dk_z.
3. On the confined ground mode, the slice-odd axial operators.

Usage: python3 tools/axial_ward.py
"""
import numpy as np
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
# periodic free walk: H(k) = H0 - sum_j (e^{ik_j} c_j + e^{-ik_j} c_j^dag)  (8x8 per k)
def Hk(k):
    M=H0.astype(complex).copy()
    for j in range(3): M-= np.exp(1j*k[j])*c[j]+np.exp(-1j*k[j])*c[j].conj().T
    return M
S=np.diag([1]*4+[-1]*4).astype(complex)     # slice sign
G5=bd(gam)
cands={'gamma5 per slice':G5,'slice sign':S,'slice sign x gamma5':S@G5}
for name,Q in cands.items():
    r=[]
    for k in ([0,0,0],[0.3,0,0],[np.pi/4]*3,[1,0.5,0.2]):
        h=Hk(k); r.append(np.linalg.norm(h@Q-Q@h)/np.linalg.norm(h))
    print('%-20s |[H(k),Q]|/|H| at k=0, .3, pi/4, mixed:'%name,' '.join('%.3f'%x for x in r))
# zero mode chirality at k=0
w,v=np.linalg.eigh(Hk([0,0,0])); print('k=0 energies',np.round(w,3))
lo=v[:,np.argsort(abs(w))[:2]]
for name,Q in cands.items(): print(name,'on lowest |E| pair',np.round(np.linalg.eigvalsh(lo.conj().T@Q@lo),3))
print('--- confined ground mode, axial = slice sign x gamma5 ---')
for n in (3,4,5,6,8):
    Ns=[]
    for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
    V=n**3; H=np.kron(np.eye(V),H0)-sum(Ns)
    Z=np.kron(np.diag([x[2] for x in sites]).astype(float),np.eye(8)); vz=1j*(H@Z-Z@H)
    Q=np.kron(np.eye(V),S@G5); Sz=np.kron(np.eye(2*V),Sz4)
    w,Vv=np.linalg.eigh(H); pos=w>1e-7; e0=w[pos].min(); sel=np.isclose(w,e0,atol=1e-6); sub=Vv[:,sel]
    Sm=sub.conj().T@Sz@sub; ws,vs=np.linalg.eigh((Sm+Sm.conj().T)/2); up=sub@vs[:,-1]
    ex=lambda O:(up.conj()@O@up).real
    Sl=np.kron(np.eye(V),S)
    print(n,'Sz %.4f | S.Sz (on-site) %.4f | link sym(Q v_z) %.4f | slice weights %.3f/%.3f'%(ex(Sz),ex(Sl@Sz),-ex((Q@vz+vz@Q)/2),ex((np.eye(8*V)+Sl)/2),ex((np.eye(8*V)-Sl)/2)))

print('--- free carrier along z: continuum <A^z> = 1 ---')
Sz8=bd(Sz4); G5=bd(gam)
for kz in (0.05,0.2,np.pi/4,1.2):
    k=[0,0,kz]; h=Hk(k); w,v=np.linalg.eigh(h)
    dk=1e-6; vz=(Hk([0,0,kz+dk])-Hk([0,0,kz-dk]))/(2*dk)
    i=np.argsort(w); posi=[j for j in i if w[j]>1e-9][:2]
    sub=v[:,posi]; m=sub.conj().T@Sz8@sub; ww,vv=np.linalg.eigh((m+m.conj().T)/2); up=sub@vv[:,-1]
    print('kz %.3f E %.4f  <Sz> %.4f  <sym g5 v_z> %.4f  group v %.4f'%(kz,w[posi[0]],(up.conj()@Sz8@up).real,(up.conj()@((G5@vz+vz@G5)/2)@up).real,(up.conj()@vz@up).real))
