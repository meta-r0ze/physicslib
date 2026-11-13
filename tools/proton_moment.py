#!/usr/bin/env python3
"""The proton's magnetic moment from the confined carrier (comparison tool).

The vector current is conserved, so unlike the axial current its normalization is fixed; the
magnetic moment therefore tests the carrier's size and the current operator without a Z factor.
Spin-flavour (SU(6)) gives mu_p = mu_0 and mu_n = -(2/3) mu_0, with mu_0 the moment of a
unit-charge carrier in the spin-up ground mode: mu_0 = <(r x J)_z>/2. J is either the link
current v = i[H, r] (what a gauge field couples to) or the on-site alpha. The spacing a is fixed by
the carrier rms radius = E8 proton radius D hbar/(m_p c). Nuclear magnetons: x 2 m_p a.

Usage: python3 tools/proton_moment.py
"""
import numpy as np
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
for n in (3,4,5,6):
    Ns=[];
    for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
    V=n**3; H=np.kron(np.eye(V),H0)-sum(Ns); c0=(n-1)/2
    X=[np.kron(np.diag([x[j]-c0 for x in sites]).astype(float),np.eye(8)) for j in range(3)]
    v=[1j*(H@X[j]-X[j]@H) for j in range(3)]
    al8=[np.kron(np.eye(2*V),a) for a in al]
    w,Vv=np.linalg.eigh(H); pos=w>1e-7; e0=w[pos].min(); sel=np.isclose(w,e0,atol=1e-6); sub=Vv[:,sel]
    Sz=np.kron(np.eye(2*V),Sz4); S=sub.conj().T@Sz@sub; ws,vs=np.linalg.eigh((S+S.conj().T)/2); up=sub@vs[:,-1]
    d=(abs(up)**2).reshape(V,8).sum(1); rho=np.sqrt(sum(d[i]*sum((q-c0)**2 for q in x) for i,x in enumerate(sites)))
    def mom(J):
        Mz=(X[0]@J[1]-X[1]@J[0]+J[1]@X[0]-J[0]@X[1])/4   # symmetrized (r x J)_z /2
        return (up.conj()@Mz@up).real
    a_fm=0.841236/rho; f=2*938.272*a_fm/197.327
    print(n,'rho %.3f a %.3f fm | mu_p link %.3f  onsite %.3f n.m. (measured 2.793; mu_n = -2/3 mu_p)'%(rho,a_fm,f*abs(mom(v)),f*abs(mom(al8))))
