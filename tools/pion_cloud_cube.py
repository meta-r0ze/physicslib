#!/usr/bin/env python3
"""Pion cloud of the confined three-carrier nucleon, no free parameters (comparison tool).

Carrier: the spin-up/down ground doublet of the 3^3 confined walk (ConfinedCarrier, hard wall).
Pion source: derivative coupling (1/2F) A^i_a d_i pi_a with the on-site axial density of the
ground doublet (sum = <Sigma_z> = 0.826) placed on the cube's interior links. No 5/4 enters: the
vertex uses the bare cube current. Inputs: 1/a = 317.5 MeV (carrier rms radius = E8 r_p),
E8 F_pi = f_pi/sqrt2 = 92.12 MeV, m_pi = 138 MeV.

Spin-flavour: three carriers in the common orbital span Sym^3(4) = N (4) + Delta (16), both at
3E0; the static second-order dressing is computed on these 20 states, with an optional N-Delta
splitting in the energy denominators. Degenerate limit: dg_A/g_A = -8c (double commutator = G on
the full multiplet), Delta - N = 24 c2 from the self-energy -16 c2 sum G^2.

Two premises for the pion's boundary (PMAction REVIEW A.3):
  field confined:  pion modes = graph (Neumann, no link out) Laplacian on the cube sites;
  source confined: pion on the unbounded lattice at the same spacing (Brillouin-zone sum).

Usage: python3 tools/pion_cloud_cube.py [n=3] [1/a MeV=317.5] [m_pi=138] [k-grid=12]
"""
import numpy as np, itertools, sys
src=open('tools/confined_walk.py').read().split('for n in (3,5):')[0]
exec(src)
n=int(sys.argv[1]) if len(sys.argv)>1 else 3
Ns=[]
for j in range(3): M,sites=Nw(n,j,'0'); Ns.append(M)
V=n**3; H=np.kron(np.eye(V),H0)-sum(Ns); idx={x:i for i,x in enumerate(sites)}
w,Vv=np.linalg.eigh(H); pos=w>1e-9; e0=w[pos].min(); sub=Vv[:,np.isclose(w,e0,atol=1e-8)]
Sz=np.kron(np.eye(2*V),Sz4); m=sub.conj().T@Sz@sub; ws,vs=np.linalg.eigh((m+m.conj().T)/2)
up=sub@vs[:,1]; dn=sub@vs[:,0]
Sx4=-1j*al[1]@al[2]; Sy4=-1j*al[2]@al[0]; Sig=[Sx4,Sy4,Sz4]
# fix relative phase so <up|Sx|dn> real positive
x01=up.conj()@np.kron(np.eye(2*V),Sx4)@dn; dn=dn*np.conj(x01)/abs(x01)
gnd=[up,dn]
# site-resolved axial densities D[i][x] = 2x2 matrix <s'|Sigma^i(x)|s>
def site_op(i,x):
    P=np.zeros((V,V)); P[x,x]=1; return np.kron(P,np.kron(np.eye(2),Sig[i]))
D=np.zeros((3,V,2,2),complex)
for i in range(3):
    for x in range(V):
        O=site_op(i,x)
        for a in range(2):
            for b in range(2): D[i,x,a,b]=gnd[a].conj()@O@gnd[b]
print('sum_x D_z (spin-z) =',np.round(D[2].sum(0)[0,0].real,4))
# pion: no link out of the cube -> graph (Neumann) Laplacian on the n^3 sites
L=np.zeros((V,V))
for x in sites:
    for j in range(3):
        y=list(x); y[j]+=1
        if y[j]<n:
            a,b=idx[x],idx[tuple(y)]; L[a,a]+=1;L[b,b]+=1;L[a,b]-=1;L[b,a]-=1
lam,phi=np.linalg.eigh(L)
# derivative coupling on interior links: (1/2F) sum_links rho^i_link (pi(y)-pi(x))/a
pauli=[np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.array([[1,0],[0,-1]])]
def Bvec(k):
    O=np.zeros((2,2),complex)
    for x in sites:
        for j in range(3):
            y=list(x); y[j]+=1
            if y[j]<n:
                a,b=idx[x],idx[tuple(y)]
                O+= (D[j,a]+D[j,b])/2*(phi[b,k]-phi[a,k])
    return np.array([np.trace(O@p).real/2 for p in pauli]), O
ainv=float(sys.argv[2]) if len(sys.argv)>2 else 317.5   # MeV
F=92.12; mpi=float(sys.argv[3]) if len(sys.argv)>3 else 138.0
c3=0; c2=0
for k in range(V):
    if lam[k]<1e-9: continue           # constant mode: zero gradient
    B,O=Bvec(k)
    om=np.sqrt(mpi**2+lam[k]*ainv**2)
    B2=(abs(B)**2).sum()/3*ainv**5      # isotropic average |B^j|^2, units a^-5 -> MeV^5 (phi orthonormal on sites: pi = phi/a^(3/2))
    c3+=B2/(8*F**2*om**3); c2+=B2/(8*F**2*om**2)
print('n %d  1/a %.1f MeV  m_pi %.1f  F %.2f'%(n,ainv,mpi,F))
print('vertex+normalization (N and Delta degenerate): dg_A/g_A = -8c = %.4f'%(-8*c3))
print('self-energy: -16 c2 sum G^2 ; Delta - N = 24 c2 = %.1f MeV  (observed 293)'%(24*c2))
print('nucleon-only intermediate states would give %.4f'%(-8*c3*25/9))

# --- with an N-Delta splitting s in the intermediate states (20-dim spin-flavour space) ---
s_=[np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.array([[1,0],[0,-1]])]
I2=np.eye(2); I4=np.eye(4)
def one(op,q):
    mm=[I4,I4,I4]; mm[q]=op; return np.kron(np.kron(mm[0],mm[1]),mm[2])
X={(j,a):sum(one(np.kron(s_[j],s_[a]),q) for q in range(3)) for j in range(3) for a in range(3)}
Sop=[sum(one(np.kron(s_[i],I2),q) for q in range(3))/2 for i in range(3)]
P=np.zeros((64,64))
for perm in itertools.permutations(range(3)):
    M=np.zeros((64,64))
    for ix in itertools.product(range(4),repeat=3):
        jx=ix[perm[0]]*16+ix[perm[1]]*4+ix[perm[2]]; M[jx,ix[0]*16+ix[1]*4+ix[2]]=1
    P+=M/6
ww,vv=np.linalg.eigh(P); Bs=vv[:,ww>0.5]
r=lambda O:Bs.conj().T@O@Bs
Xr={k:r(o) for k,o in X.items()}
S2=sum(r(o)@r(o) for o in Sop); es,us=np.linalg.eigh(S2)
PN=us[:,np.isclose(es,0.75)]; PD=us[:,np.isclose(es,3.75)]
Sz_r=r(Sop[2])
A=Xr[(2,0)]/4   # G^{z,1}: isovector axial (tau_1) as representative
# nucleon spin-up states: diagonalize Sz in N
mz=PN.conj().T@Sz_r@PN; ez,uz=np.linalg.eigh(mz); Nup=PN@uz[:,np.isclose(ez,0.5)]   # 2 states (isospin)
modes=[]
for k in range(V):
    if lam[k]<1e-9: continue
    B,O=Bvec(k); om=np.sqrt(mpi**2+lam[k]*ainv**2); modes.append(((abs(B)**2).sum()/3*ainv**5,om))
def dressed_ratio(split):
    H0s=split*(PD@PD.conj().T)          # Delta energy above N
    # first-order dressed states |N> - sum_{k,a,j} (H0s+om)^-1 V |N>, V = c_k B^j X^{ja}
    num=0; nrm=0
    base=np.array(Nup)
    # A expectation in a fixed nucleon state |N up, isospin component>; use Gram over the 2-state block
    tot=Nup.conj().T@A@Nup; corrA=np.zeros_like(tot); corrN=np.zeros_like(tot)
    for B2,om in modes:
        coef=B2/(8*F**2*om)                 # |c B^j|^2 per component (isotropic)
        Rinv=np.linalg.inv(H0s+om*np.eye(20))
        for j in range(3):
            for a in range(3):
                Vv_=Xr[(j,a)]
                psi=Rinv@Vv_@Nup             # admixture (one pion of type k,a)
                corrA+=coef*(psi.conj().T@A@psi)
                corrN+=coef*(psi.conj().T@psi)
    # <A> = (A0 + corrA)/(1 + corrN) ; isospin-off-diagonal block: use trace ratio
    a0=np.trace(tot@tot.conj().T).real
    val=np.trace((tot+corrA-0.5*(corrN@tot+tot@corrN))@tot.conj().T).real
    return val/a0-1
for split in (0,172.4,293):
    print('N-Delta splitting %5.1f MeV in denominators: dg_A/g_A = %.4f'%(split,dressed_ratio(split)))

# --- comparison premise: host confines only the source; pion on the unbounded lattice (same spacing)
links=[]
for x in sites:
    for j in range(3):
        y=list(x); y[j]+=1
        if y[j]<n: links.append((idx[x],idx[tuple(y)],np.array(x,float),np.array(y,float),j))
Dz=[np.array([np.trace(D[j,xx]@s_[2]).real/2 for xx in range(V)]) for j in range(3)]  # spin-z projected densities
def Bz_of_k(kv):
    # z-spin component of the source for a plane wave e^{ik.x} (unit-normalized per site)
    tot=0j
    for a,b,xa,xb,j in links:
        tot+=(Dz[j][a]+Dz[j][b])/2*(np.exp(1j*kv@xb)-np.exp(1j*kv@xa))
    return tot
Nk=int(sys.argv[4]) if len(sys.argv)>4 else 16
ks=(np.arange(Nk)+0.5)/Nk*2*np.pi-np.pi
c3f=0
for k1 in ks:
    for k2 in ks:
        for k3 in ks:
            kv=np.array([k1,k2,k3]); om=np.sqrt(mpi**2+ainv**2*sum(4*np.sin(kv/2)**2))
            # isotropic average over the 3 spin components ~ |B_z|^2 averaged over directions of k
            c3f+=abs(Bz_of_k(kv))**2*ainv**5/(8*F**2*om**3)
c3f/=Nk**3   # (1/N^3) sum = a^3 int d^3k/(2pi)^3 on the zone
print('source-confined, pion on the unbounded lattice: dg_A/g_A = -8c = %.4f (degenerate N, Delta)'%(-8*c3f))
modes_f=[]; c2f=0
for k1 in ks:
    for k2 in ks:
        for k3 in ks:
            kv=np.array([k1,k2,k3]); om=np.sqrt(mpi**2+ainv**2*sum(4*np.sin(kv/2)**2))
            b2=abs(Bz_of_k(kv))**2*ainv**5/Nk**3
            modes_f.append((b2,om)); c2f+=b2/(8*F**2*om**2)
print('  self-energy Delta - N = 24 c2 = %.1f MeV'%(24*c2f))
modes=modes_f
for split in (0,100,293):
    print('  N-Delta splitting %5.1f MeV in denominators: dg_A/g_A = %.4f'%(split,dressed_ratio(split)))
