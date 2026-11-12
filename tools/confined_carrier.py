#!/usr/bin/env python3
"""Confined two-slice domain-wall carrier (comparison tool, not a Lean theorem).

The Hamiltonian is PMAction.DomainWall's, built on a finite cube; PMAction.ConfinedCarrier
holds the algebraic facts. It has two D4 sectors (slices). Each has the 3D Wilson-Dirac
Hamiltonian with hop alpha_j/(2i) - r*beta/2 and on-site (3r + r - M)*beta, plus a
confinement mass Mout outside the inner 3^3 cube. The slices are joined by
-(i*alpha_4 + r*beta)/2, at the Wilson point M = r = 1.

The script prints the lowest positive level, its degeneracy, the largest <Sigma_z> in that
level, and (5/3)<Sigma_z> with the count 5/3 from PMHadrons.AxialCount. That is a single
free carrier's value, not the neutron's g_A.

Usage: python3 tools/confined_carrier.py n Mout [Mout ...]
  n = 3, Mout = 0: hard wall on the 3^3 cube   -> E0 0.841, <Sz> 0.8260, (5/3)<Sz> 1.377
  n = 5, Mout = 3 / 10 / 100: soft walls       -> <Sz> 0.802 / 0.822 / 0.826
The physical wall is hard (M_out = infinity, see PMAction.ConfinedCarrier); soft walls are
sensitivity checks.
"""
import numpy as np, itertools, sys
sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]]); sz=np.diag([1,-1]).astype(complex); I2=np.eye(2)
al=[np.kron(sx,s) for s in (sx,sy,sz)]; be=np.kron(sz,I2); a4=np.kron(sy,I2); Sz=np.kron(I2,sz)
def H(n,inner,Mout,M=1.0,r=1.0):
  N=n**3; idx=lambda c:c[0]+n*c[1]+n*n*c[2]; lo=(n-inner)//2
  hs=np.zeros((4*N,4*N),complex)
  for c in itertools.product(range(n),repeat=3):
    i=idx(c); inside=all(lo<=x<lo+inner for x in c)
    hs[4*i:4*i+4,4*i:4*i+4]+=(3*r+(r-M)+(0 if inside else Mout))*be
    for j in range(3):
      d=list(c); d[j]+=1
      if d[j]<n:
        k=idx(d); hop=al[j]/(2j)-r*be/2
        hs[4*k:4*k+4,4*i:4*i+4]+=hop; hs[4*i:4*i+4,4*k:4*k+4]+=hop.conj().T
  h=np.kron(np.eye(2),hs); blk=np.kron(np.eye(N),-(1j*a4+r*be)/2)
  h[4*N:,:4*N]+=blk; h[:4*N,4*N:]+=blk.conj().T
  return h,N
n=int(sys.argv[1])
for Mout in map(float,sys.argv[2:]):
  h,N=H(n,3,Mout); w,V=np.linalg.eigh(h); pos=np.where(w>1e-9)[0]; e0=w[pos[0]]
  sub=V[:,np.isclose(w,e0,atol=1e-6)]
  S=sub.conj().T@np.kron(np.eye(2*N),Sz)@sub; s=np.linalg.eigvalsh(S).max()
  print('n',n,'Mout',Mout,'E0 %.3f deg %d <Sz> %.4f (5/3)Sz %.4f'%(e0,sub.shape[1],s,5/3*s),flush=True)
