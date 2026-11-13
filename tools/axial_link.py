#!/usr/bin/env python3
"""Which axial operator: on-site Sigma_z vs the link (gauge-coupled) current (comparison tool).

A gauge boson couples to a lattice walk through its links: the spatial current is the velocity
operator v_z = i[H, z] (point-split), not the on-site alpha_z. The axial spatial current is then
gamma5 v_z (symmetrized). For the confined carrier (PMAction.ConfinedCarrier, hard wall) this
prints, per cube edge n, the on-site <Sigma_z> and the link <gamma5 v_z> in the spin-up ground
mode. Sign: H = H0 - sum N_j, so v_z -> -alpha_z at small momentum.

Usage: python3 tools/axial_link.py
"""
import numpy as np, itertools
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
g5=bd(gam)
for n in (3,4,5,6,8):
    Ns=[];
    for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
    V=n**3; H=np.kron(np.eye(V),H0)-sum(Ns)
    Z=np.kron(np.diag([x[2] for x in sites]).astype(float),np.eye(8))
    vz=1j*(H@Z-Z@H)
    Az=(np.kron(np.eye(V),g5)@vz+vz@np.kron(np.eye(V),g5))/2
    Sz=np.kron(np.eye(2*V),Sz4)
    w,Vv=np.linalg.eigh(H); pos=w>1e-7; e0=w[pos].min(); sel=np.isclose(w,e0,atol=1e-6); sub=Vv[:,sel]
    S=sub.conj().T@Sz@sub; ws,vs=np.linalg.eigh((S+S.conj().T)/2); up=sub@vs[:,-1]
    print(n,'Sz %.4f  <g5 v_z> %.4f  <v_z> %.1e  ratio %.4f'%((up.conj()@Sz@up).real,(up.conj()@Az@up).real,abs(up.conj()@vz@up),(up.conj()@Az@up).real/(up.conj()@Sz@up).real))
