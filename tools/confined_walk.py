#!/usr/bin/env python3
"""Confined split-step walk: face closures of PMAction's split update (comparison tool).

PMAction's substrate update (SplitUpdate, WilsonSplit) is the on-site coin
exp(-i tau H0) times one rotation cos(tau) + i sin(tau) N_j per axis. N_j must be a
Hermitian involution (N_j^2 = 1): that is what makes each step exactly unitary and
strictly local. On a periodic lattice N_j = P (x) c_j + P^T (x) c_j^dag, with
c_j = beta/2 + i alpha_j/2 (LocalUnitary.coefficient).

On a finite cube the truncated hop is not an involution. The face sites lack
c_j^dag c_j (far face) or c_j c_j^dag (near face). The only completion keeping N_j
local and involutive adds, on each face, a Hermitian involution W restricted to the
range of that projector. Note c_j^dag c_j = (1 + i beta alpha_j)/2, the lattice form of
the MIT bag projector (1 + i beta alpha.n)/2 for the outward normal n.

W is not fixed by unitarity. This script compares closures by the tau -> 0
generator H0 - sum_j N_j (the walk's Hamiltonian), on n^3 cubes:
  s=0 (plain truncation, not a walk), +1, -1, per-sector (+,-), and W = Sigma_normal.
For each it lists the lowest positive levels: energy, degeneracy, <Sigma_z>, and the
centre weight (the fraction on interior sites).

Selection (PMAction.CompletionSelection). That theorem is about the *update*: the modes
an update does not reach evolve by the identity. Applied per axis step, R_j acts as the
rotation cos(tau) + i sin(tau) N_t on the modes the truncated hop N_t covers (there
N_t^2 = 1), and as the identity on the face modes P_j = 1 - N_t^2 it misses. R_j is
unitary and local, and its generator is the plain truncation: s = 0 here, the 0.826 carrier.
Completing N_j itself by P W P (W = +-1, ...) instead adds an on-site +-1/2 potential on the
faces, which binds the surface states seen below. That is not the selected completion.
The second table classifies levels by the cube double-group irrep (C4 about z). The third
runs Paper II's vacuum-preserving update (e^{-i tau W} R_beta^dag^3 R_0 R_1 R_2) at finite
tick tau. The spin fraction then depends on the axis (<Sx>, <Sy>, <Sz> differ), the same
ordering anisotropy as Paper II's v_j(tau) = sin tau (cos 5tau, cos 3tau, cos tau). Only
tau -> 0 keeps the cube's isotropy; there all three equal 0.826.

Usage: python3 tools/confined_walk.py
"""
import numpy as np, itertools, sys

I=1j
beta=np.array([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]],complex)
gam=np.diag([1,1,-1,-1]).astype(complex)
al=[np.array([[0,1,0,0],[1,0,0,0],[0,0,0,-1],[0,0,-1,0]],complex),
    np.array([[0,-I,0,0],[I,0,0,0],[0,0,0,I],[0,0,-I,0]],complex),
    np.diag([1,-1,-1,1]).astype(complex)]
Sz4=-I*al[0]@al[1]
def bd(A): Z=np.zeros((8,8),complex); Z[:4,:4]=A; Z[4:,4:]=A; return Z
hop=-beta@(np.eye(4)+gam)/2; back=-beta@(np.eye(4)-gam)/2
H0=np.block([[3*beta,hop],[back,3*beta]])
c=[bd(beta/2+I*a/2) for a in al]
def N(n,j,s):
  sites=list(itertools.product(range(n),repeat=3)); idx={x:i for i,x in enumerate(sites)}
  M=np.zeros((8*len(sites),)*2,complex)
  for x in sites:
    i=idx[x]; y=list(x); y[j]+=1
    if y[j]<n:
      k=idx[tuple(y)]; M[8*k:8*k+8,8*i:8*i+8]+=c[j]; M[8*i:8*i+8,8*k:8*k+8]+=c[j].conj().T
    if x[j]==n-1: M[8*i:8*i+8,8*i:8*i+8]+=s*c[j].conj().T@c[j]
    if x[j]==0:   M[8*i:8*i+8,8*i:8*i+8]+=s*c[j]@c[j].conj().T
  return M,len(sites)
def run(n,tau,s):
  Ns=[N(n,j,s)[0] for j in range(3)]; V=len(Ns[0])//8
  for M in Ns: assert np.allclose(M@M,np.eye(len(M))) and np.allclose(M,M.conj().T)
  w0,V0=np.linalg.eigh(H0); Q=np.kron(np.eye(V),V0@np.diag(np.exp(-I*tau*w0))@V0.conj().T)
  if tau==0:
    Heff=np.kron(np.eye(V),H0)-sum(Ns); w,Vv=np.linalg.eigh(Heff); om=w
  else:
    R=[np.cos(tau)*np.eye(len(M))+I*np.sin(tau)*M for M in Ns]
    U=Q@R[0]@R[1]@R[2]
    ev,Vv=np.linalg.eig(U); om=-np.angle(ev)/tau
  pos=np.where(om>1e-7)[0]; e0=om[pos].min()
  sel=np.isclose(om,e0,atol=1e-6); sub=np.linalg.qr(Vv[:,sel])[0]
  Sz=np.kron(np.eye(2*V),Sz4)
  S=sub.conj().T@Sz@sub; sv=np.linalg.eigvalsh((S+S.conj().T)/2).max()
  print('n',n,'tau',tau,'s',s,'E0 %.4f deg %d <Sz> %.4f (5/3)Sz %.4f'%(e0,sel.sum(),sv,5/3*sv),flush=True)
Sig=[-I*al[1]@al[2],-I*al[2]@al[0],-I*al[0]@al[1]]
def Wmat(kind,j):
  if kind=='0': return np.zeros((8,8),complex)
  if kind=='+': return np.eye(8)
  if kind=='-': return -np.eye(8)
  if kind=='+-': return np.diag([1]*4+[-1]*4).astype(complex)
  if kind=='-+': return np.diag([-1]*4+[1]*4).astype(complex)
  if kind=='Sig': return bd(Sig[j])
def Nw(n,j,kind):
  sites=list(itertools.product(range(n),repeat=3)); idx={x:i for i,x in enumerate(sites)}
  M=np.zeros((8*len(sites),)*2,complex); W=Wmat(kind,j)
  Pend=c[j].conj().T@c[j]; P0=c[j]@c[j].conj().T
  for x in sites:
    i=idx[x]; y=list(x); y[j]+=1
    if y[j]<n:
      k=idx[tuple(y)]; M[8*k:8*k+8,8*i:8*i+8]+=c[j]; M[8*i:8*i+8,8*k:8*k+8]+=c[j].conj().T
    if x[j]==n-1: M[8*i:8*i+8,8*i:8*i+8]+=Pend@W@Pend
    if x[j]==0:   M[8*i:8*i+8,8*i:8*i+8]+=P0@W@P0
  if kind!='0': assert np.allclose(M@M,np.eye(len(M))),kind
  else: assert np.allclose(M@M@M,M)  # truncated hop: N^3 = N (ConfinedCarrier.axisStep_unitary)
  return M,sites
for n in (3,5):
 for kind in ['0','+','-','+-','Sig']:
  Ns=[];
  for j in range(3): M,sites=Nw(n,j,kind); Ns.append(M)
  V=len(sites); Heff=np.kron(np.eye(V),H0)-sum(Ns); w,Vv=np.linalg.eigh(Heff)
  Sz=np.kron(np.eye(2*V),Sz4); inner=[i for i,x in enumerate(sites) if all(0<q<n-1 for q in x)]
  out=[];done=set()
  for e in w[w>1e-7][:30]:
    if round(e,5) in done: continue
    done.add(round(e,5)); sel=np.isclose(w,e,atol=1e-6); sub=Vv[:,sel]
    S=sub.conj().T@Sz@sub; sv=np.linalg.eigvalsh((S+S.conj().T)/2).max()
    A=(abs(sub)**2).sum(1).reshape(V,2,4)/sel.sum()
    out.append('E %.3f d%d Sz %.3f ctr %.2f'%(e,sel.sum(),sv,A.sum((1,2))[inner].sum()))
    if len(out)>=5: break
  print(n,kind,' | '.join(out),flush=True)

print('--- cube irreps (C4 about z) ---')
def expm_h(A,t):  # exp(-i t A) for Hermitian A
  w,V=np.linalg.eigh(A); return V@np.diag(np.exp(-1j*t*w))@V.conj().T
Rs=expm_h(Sz4,np.pi/4)   # spinor rotation by pi/2 about z
assert np.allclose(Rs@al[0]@Rs.conj().T,al[1])
def C4(n,sites):
  idx={x:i for i,x in enumerate(sites)}; V=len(sites); P=np.zeros((V,V))
  for x in sites:
    y=(n-1-x[1],x[0],x[2])  # (x,y)->(-y,x) about centre
    P[idx[y],idx[x]]=1
  return np.kron(P,bd(Rs))
for kind in ['0','+','-','+-']:
 for n in (3,4,5):
  Ns=[];
  for j in range(3): M,sites=Nw(n,j,kind); Ns.append(M)
  V=len(sites); Heff=np.kron(np.eye(V),H0)-sum(Ns); w,Vv=np.linalg.eigh(Heff)
  C=C4(n,sites); comm=np.abs(C@Heff-Heff@C).max()
  Sz=np.kron(np.eye(2*V),Sz4); out=[];done=set()
  for e in w[w>1e-7][:40]:
    if round(e,5) in done: continue
    done.add(round(e,5)); sel=np.isclose(w,e,atol=1e-6); sub=Vv[:,sel]
    chi=np.trace(sub.conj().T@C@sub)
    S=sub.conj().T@Sz@sub; sv=np.linalg.eigvalsh((S+S.conj().T)/2).max()
    lab={2:'G6' if chi.real>0.5 else ('G7' if chi.real<-0.5 else 'G?'),4:'G8'}.get(sel.sum(),'?')
    out.append('E %.3f %s Sz %.3f'%(e,lab,sv))
    if len(out)>=4: break
  print(kind,n,'comm %.1e'%comm,' | '.join(out),flush=True)

print('--- Paper II corrected update at finite tau (identity face completion) ---')
Wm=np.block([[np.zeros((4,4)),hop],[back,np.zeros((4,4))]]); b8=bd(beta)
Sx4=-1j*al[1]@al[2]; Sy4=-1j*al[2]@al[0]
def expmh(A,t):
  w,Vh=np.linalg.eigh(A); return Vh@np.diag(np.exp(-1j*t*w))@Vh.conj().T
n=3
Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=len(sites); D=8*V
for tau in (0.0,0.02,0.05,0.1,0.2,0.3,0.5):
  if tau==0:
    w,Vv=np.linalg.eigh(np.kron(np.eye(V),H0)-sum(Ns)); om=w
  else:
    Rb=np.cos(tau)*np.eye(8)+1j*np.sin(tau)*b8
    U=np.kron(np.eye(V),expmh(Wm,tau)@np.linalg.matrix_power(Rb.conj().T,3))
    for M in Ns:
      Qj=M@M; U=U@(np.cos(tau)*Qj+1j*np.sin(tau)*M+(np.eye(D)-Qj))
    assert np.allclose(U.conj().T@U,np.eye(D))
    ev,Vv=np.linalg.eig(U); om=-np.angle(ev)/tau
  e=om[om>1e-7].min(); sel=np.isclose(om,e,atol=1e-6); sub=np.linalg.qr(Vv[:,sel])[0]
  out=[]
  for Sg in (Sx4,Sy4,Sz4):
    S=sub.conj().T@np.kron(np.eye(2*V),Sg)@sub; out.append(np.linalg.eigvalsh((S+S.conj().T)/2).max())
  print(n,'tau',tau,'E %.4f deg %d  <Sx> %.4f <Sy> %.4f <Sz> %.4f'%(e,sel.sum(),*out),flush=True)

print('--- lattice scale from the E8 proton radius (PMHadrons.protonRadius_value) ---')
n=3; Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=len(sites); w,Vv=np.linalg.eigh(np.kron(np.eye(V),H0)-sum(Ns))
e=w[w>1e-7].min(); sel=np.isclose(w,e,atol=1e-6); sub=Vv[:,sel]
rho=(abs(sub)**2).sum(1).reshape(V,8).sum(1)/sel.sum()
rms=np.sqrt(sum(rho[i]*sum((x-1)**2 for x in s) for i,s in enumerate(sites)))
rp=0.8412356; hbarc=197.3269804; a=rp/rms
print('carrier rms %.4f sites; a = r_p/rms = %.4f fm; 1/a = %.1f MeV; E0 = %.1f MeV; 3 E0 = %.0f MeV'%(rms,a,hbarc/a,e*hbarc/a,3*e*hbarc/a))
