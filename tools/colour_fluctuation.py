#!/usr/bin/env python3
"""One-gluon exchange among the three confined carriers (comparison tool, not a Lean theorem).

Three carriers in the ground spin-1/2 mode of the confined walk on the 3^3 cube
(PMAction.ConfinedCarrier, ConfinedWalk: hard wall, small tick), colour singlet (pair colour
factor -2/3, PMAction.ColourSinglet's eps algebra), interacting through the static exchange
V_ij = g^2 sum_xy G(x,y) [rho_i(x) rho_j(y) - J_i(x).J_j(y)], with G the exact Dirichlet Green
function of the cube (PMAction.CubeGreen3) and J = psi^dag alpha psi.

Boundary conditions for the colour field (Nov 2026). Default (BC=N): the persistence rule used
for the carrier (only the hadron's own sites and links are refreshed; links out of the cube are
not its resources) removes the links out of the cube. For the static electric part that is the
Neumann Laplacian (n.E = 0, no colour flux leaves); for the magnetic part, component k has no
link out along axis k (A_k = 0 there) and Neumann along the other axes (n x B = 0). These are
the bag-model conditions, here from the lattice rule. BC=D keeps the earlier Dirichlet G
(field zero on outside sites), which connects the cube to unrefreshed sites.

Computes, at first order (positive-energy intermediate modes only):
  * the change of g_A = <p| sum tau+ Sigma_z |n> from mixing ground with excited modes;
  * the N-Delta splitting from the ground-sector interaction.
Both are linear in g^2, so their ratio is coupling-free.

Usage: [BC=D] python3 tools/colour_fluctuation.py [alpha_s]   (default 0.1180, the ledger value)
"""
import sys, itertools, os, numpy as np
src=open("tools/confined_walk.py").read().split('for n in (3,5):')[0]
exec(src)
n=3; Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=len(sites); D=8*V
H=np.kron(np.eye(V),H0)-sum(Ns)
idx={x:i for i,x in enumerate(sites)}
Lap=6*np.eye(V)
for x in sites:
  for j in range(3):
    for d in (-1,1):
      y=list(x); y[j]+=d
      if 0<=y[j]<n: Lap[idx[x],idx[tuple(y)]]-=1
import os
if os.environ.get('BC','N')=='N':
  Lap2=np.zeros((V,V))
  for x in sites:
    for j in range(3):
      for d in (-1,1):
        y=list(x); y[j]+=d
        if 0<=y[j]<n: Lap2[idx[x],idx[tuple(y)]]-=1; Lap2[idx[x],idx[x]]+=1
  ww_,vv_=np.linalg.eigh(Lap2); keep=ww_>1e-9; G=(vv_[:,keep]/ww_[keep])@vv_[:,keep].T
else:
  G=np.linalg.inv(Lap)
def lapmix(k):  # component k: Dirichlet along axis k (normal links absent beyond wall -> A_k = 0 there), Neumann along others
  M=np.zeros((V,V))
  for x in sites:
    for j in range(3):
      for d in (-1,1):
        y=list(x); y[j]+=d
        if 0<=y[j]<n: M[idx[x],idx[tuple(y)]]-=1; M[idx[x],idx[x]]+=1
        elif j==k: M[idx[x],idx[x]]+=1
  return M
if os.environ.get('BC','N')=='N':
  GM=[np.linalg.inv(lapmix(k)) for k in range(3)]
else:
  GM=[G,G,G]
w,Vv=np.linalg.eigh(H)
pos=np.where(w>1e-7)[0]; e0=w[pos].min()
gs=np.where(np.isclose(w,e0,atol=1e-6))[0]; assert len(gs)==2
exc=[i for i in pos if i not in gs]
SzD=np.kron(np.eye(2*V),Sz4)
SxD=np.kron(np.eye(2*V),-1j*al[1]@al[2])
sub=Vv[:,gs]
# spin basis in doublet
S=sub.conj().T@SzD@sub; ws,vs=np.linalg.eigh(S)
up=sub@vs[:,1]; dn=sub@vs[:,0]
x01=up.conj()@SxD@dn; dn=dn*np.conj(x01)/abs(x01)   # make <up|Sx|dn> real positive
gnd=[up,dn]; s0=(up.conj()@SzD@up).real
print('s0 %.4f  <dn|Sz|dn> %.4f  <up|Sx|dn> %.4f'%(s0,(dn.conj()@SzD@dn).real,(up.conj()@SxD@dn).real))
alD=[np.kron(np.eye(2*V),a) for a in al]
def dens(a,b):   # site-resolved a^dag b
  return (a.conj()*b).reshape(V,8).sum(1)
def curr(a,b,k): return (a.conj()*(alD[k]@b)).reshape(V,8).sum(1)
g2=4*np.pi*float(sys.argv[1]) if len(sys.argv)>1 else 4*np.pi*0.1180
cf=-2/3
# ground-ground densities/currents for partner: g[s'][s]
gg=[[dens(gnd[a],gnd[b]) for b in range(2)] for a in range(2)]
gk=[[[curr(gnd[a],gnd[b],k) for b in range(2)] for a in range(2)] for k in range(3)]
# one-body spin-isospin: index (s,t) -> 2*s+t ; s:0 up,1 dn ; t:0 u,1 d
def onebody():
  sz=np.diag([.5,-.5]); sp=np.array([[0,1],[0,0]]); sm=sp.T
  return sz,sp,sm
sz,sp,sm=onebody(); I2=np.eye(2)
def op1(o,which,pos):   # one-body op on 4-dim space, applied at position pos in 64-dim
  O=np.kron(o,I2) if which=='s' else np.kron(I2,o)
  mats=[np.eye(4)]*3; mats=list(mats); mats[pos]=O
  return np.kron(np.kron(mats[0],mats[1]),mats[2])
def tot(o,which): return sum(op1(o,which,p) for p in range(3))
Sz_t=tot(sz,'s'); Sp_t=tot(sp,'s'); Sm_t=tot(sm,'s'); S2=Sm_t@Sp_t+Sz_t@Sz_t+Sz_t
Iz_t=tot(sz,'t'); Ip_t=tot(sp,'t'); Im_t=tot(sm,'t'); I2_t=Im_t@Ip_t+Iz_t@Iz_t+Iz_t
# symmetric projector
P=np.zeros((64,64))
for perm in itertools.permutations(range(3)):
  M=np.zeros((64,64))
  for a,b,c in itertools.product(range(4),repeat=3):
    t=[a,b,c]; u=[t[perm[0]],t[perm[1]],t[perm[2]]]
    M[u[0]*16+u[1]*4+u[2], a*16+b*4+c]=1
  P+=M/6
def state(iz):
  Q=P@np.diag(np.isclose(np.diag(Sz_t),.5)*np.isclose(np.diag(Iz_t),iz))@P
  ww,vv=np.linalg.eigh(Q); B=vv[:,ww>.5]
  X=B.T@(S2+I2_t)@B; xw,xv=np.linalg.eigh(X)
  v=B@xv[:,np.isclose(xw,1.5)]; assert v.shape[1]==1, xw
  return v[:,0]
p=state(.5); nn=state(-.5)
# A = sum_k tau+_k sigma_z_k  (spin-isospin part); radial Sz handled separately
A0=sum(op1(2*sz,'s',k)@op1(sp,'t',k) for k in range(3))
if p@A0@nn<0: nn=-nn
print('SU6 <p|sum tau+ sigz|n> =',round(p@A0@nn,4),' -> g_A0 = %.4f'%(s0*(p@A0@nn)))
pT=p.reshape(4,4,4); nT=nn.reshape(4,4,4)
# transition quantities for excited modes
Ee=w[exc]; Ph=Vv[:,exc]
SzE=np.array([[Ph[:,e].conj()@SzD@gnd[s] for s in range(2)] for e in range(len(exc))])  # <e|Sz|0s>
dE=np.array([[dens(Ph[:,e],gnd[s]) for s in range(2)] for e in range(len(exc))])        # (e,s,site)
jE=np.array([[[curr(Ph[:,e],gnd[s],k) for s in range(2)] for e in range(len(exc))] for k in range(3)])
# pair kernel K[e, s_i, s'_j, s_j]
K=np.zeros((len(exc),2,2,2),complex)
for a in range(2):
  for b in range(2):
    Ge=G@gg[a][b]
    K[:,:,a,b]+=cf*g2*np.einsum('esx,x->es',dE,Ge)
    for k in range(3):
      K[:,:,a,b]-=cf*g2*np.einsum('esx,x->es',jE[k],GM[k]@gk[k][a][b])
def ST(s,t): return 2*s+t
# delta = sum_m [<p|H|m><m|A|n> + <p|A|m><m|H|n>]/(E0-Em); positions by symmetry: excited at position 0, times 3
delta=0j
for e in range(len(exc)):
  den=e0-Ee[e]
  for ti in range(2):
    for sj,tj,sk,tk in itertools.product(range(2),repeat=4):
      J=ST(sj,tj); Kk=ST(sk,tk)
      # <m|H|psi> with carrier0 excited (e,ti), spectators (J at pos1, Kk at pos2); partner pos1 or pos2
      def Hm(T):
        amp=0j
        for si in range(2):
          for sjo in range(2):   # partner pos1 original spin
            amp+=K[e,si,sj,sjo]*T[ST(si,ti),ST(sjo,tj),Kk]
          for sko in range(2):   # partner pos2
            amp+=K[e,si,sk,sko]*T[ST(si,ti),J,ST(sko,tk)]
        return amp
      # <m|A|n>: carrier0: tau+ requires ti==u(0) from d(1); sigma -> Sz radial matrix
      Amn=0j
      if ti==0:
        for si in range(2): Amn+=SzE[e,si]*nT[ST(si,1),J,Kk]
      Apm=0j   # <p|A|m> = conj of <m|A^dag|p>; A^dag has tau-: m carrier0 t=d from p's u
      if ti==1:
        for si in range(2): Apm+=np.conj(SzE[e,si])*pT[ST(si,0),J,Kk]
      delta+=(np.conj(Hm(pT))*Amn + Apm*Hm(nT))/den
delta*=3
gA0=s0*(p@A0@nn)
print('alpha_s %.4f  g_A0 %.4f  delta(OGE, positive modes) %.4f  -> g_A %.4f (%.2f%%)'%(g2/(4*np.pi),gA0,delta.real,gA0+delta.real,100*delta.real/gA0))
print('imag part %.2e'%delta.imag)
# ground-sector pair interaction and N-Delta splitting
Vg=np.zeros((2,2,2,2),complex)   # [s'i,s'j,si,sj]
for a,b,c,d in itertools.product(range(2),repeat=4):
  Vg[a,b,c,d]=cf*g2*(gg[a][c]@G@gg[b][d]-sum(gk[k][a][c]@GM[k]@gk[k][b][d] for k in range(3)))
def Hground(T):   # sum over pairs on 3-carrier tensor (s,t) labels; flavour blind
  out=np.zeros_like(T,dtype=complex)
  for (i,j) in [(0,1),(0,2),(1,2)]:
    for idxs in itertools.product(range(4),repeat=3):
      val=T[idxs]
      if val==0: continue
      si,ti=divmod(idxs[i],2); sj,tj=divmod(idxs[j],2)
      for a in range(2):
        for b in range(2):
          o=list(idxs); o[i]=2*a+ti; o[j]=2*b+tj
          out[tuple(o)]+=Vg[a,b,si,sj]*val
  return out
def stateSI(S,I,sz_,iz):
  Q=P@np.diag(np.isclose(np.diag(Sz_t),sz_)*np.isclose(np.diag(Iz_t),iz))@P
  ww,vv=np.linalg.eigh(Q); B=vv[:,ww>.5]
  X=B.T@(S2+I2_t)@B; xw,xv=np.linalg.eigh(X)
  v=B@xv[:,np.isclose(xw,S*(S+1)+I*(I+1))]; return v[:,0]
N=stateSI(.5,.5,.5,.5); Dl=stateSI(1.5,1.5,.5,.5)
EN=(N.conj()@Hground(N.reshape(4,4,4)).ravel()).real; ED=(Dl.conj()@Hground(Dl.reshape(4,4,4)).ravel()).real
a_inv=317.5
print('ground-sector OGE: E_N %.4f E_D %.4f  Delta-N = %.4f lattice = %.1f MeV (observed 293 MeV)'%(EN,ED,ED-EN,(ED-EN)*a_inv))
print('alpha_s needed for 293 MeV: %.2f'%(0.1180*293/((ED-EN)*a_inv)))
