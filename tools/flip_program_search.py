"""Shortest class-blind flip programs (PMAction REVIEW, absolute event clock).

Model: carriers of each class as D4 weights; a root event is the reflection's permutation; a pulse of
duration tau (in units where a quarter-time q is pi/2) is exp(-i tau (1 - R)/2) (RootTransferPhase.phase),
forward only (tau in [0, 2 pi)). Target, the same program in all three classes: the certain flip
i*beta on the odd sector and the identity on the even sector, up to one common phase.
Checks run here: the library program reproduces the target at 32 q; the split 24 q program below.
Checks run once (exhaustive, minutes each; not repeated here): the library program (ClassBlindFlip.forwardPulse) costs 32 q; no program of <= 4 pulses at
quarter multiples, or <= 3 at eighth multiples; only one signed four-reflection generator has beta on
the odd sector (the library's) and no Weyl-group echo exists, so the echo must be a phase circuit; no
echo of <= 3 pulses even spans the target; with the library's echo Q the generator splits into two
commuting halves, giving a 24 q program.
"""
import itertools, numpy as np
h=0.5
V=[np.array([s*(i==j) for j in range(4)],float) for i in range(4) for s in (1,-1)]
S=[np.array(p) for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==0]
C=[np.array(p) for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==1]
cls=[V,S,C]
E=np.eye(4)
roots=[]
for a in range(4):
    for b in range(a+1,4):
        for t in (1,-1): roots.append(E[a]+t*E[b])   # 12 up to sign
def perm(M,X):
    P=np.zeros((8,8))
    for j,w in enumerate(X):
        v=M@w; i=[k for k,x in enumerate(X) if np.allclose(x,v)][0]; P[i,j]=1
    return P
refl=lambda r: np.eye(4)-np.outer(r,r)
Rm=[[perm(refl(r),X) for X in cls] for r in roots]
B=np.array([[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]],float)
Bp=[perm(B,X) for X in cls]
anti=[perm(-np.eye(4),X) for X in cls]
odd=[(np.eye(8)-A)/2 for A in anti]; even=[(np.eye(8)+A)/2 for A in anti]
theta=np.pi/2
targ=[1j*Bp[c]@odd[c]+even[c] for c in range(3)]  # exp(i pi/2 beta) on odd, 1 on even
# check beta commutes with antipode
print("beta keeps sectors:",all(np.allclose(Bp[c]@anti[c],anti[c]@Bp[c]) for c in range(3)))
def pulse(ri,tau,c):
    P=Rm[ri][c]; return np.eye(8)+(np.exp(-1j*tau)-1)*(np.eye(8)-P)/2
def matches(Us):
    # up to one common global phase
    ph=None
    for c in range(3):
        M=Us[c]@np.linalg.inv(targ[c])
        if not np.allclose(M,M[0,0]*np.eye(8),atol=1e-9): return False
        if ph is None: ph=M[0,0]
        elif not np.isclose(ph,M[0,0]): return False
    return True

print('--- library program')
def idx(r):
    r=np.array(r,float)
    for i,x in enumerate(roots):
        if np.allclose(x,r) or np.allclose(x,-r): return i
blk=[idx(E[0]-E[2]),idx(E[0]+E[2]),idx(E[1]-E[3]),idx(E[1]+E[3])]
ph=[idx(E[0]-E[1]),idx(E[0]+E[1]),idx(E[2]-E[3]),idx(E[2]+E[3])]
q=np.pi/2; x=np.pi/4
prog=[(blk[0],x),(blk[1],2*np.pi-x),(blk[2],x),(blk[3],2*np.pi-x)]+[(r,3*q) for r in ph]+\
     [(blk[0],x),(blk[1],2*np.pi-x),(blk[2],x),(blk[3],2*np.pi-x)]+[(r,q) for r in ph[::-1]]
for order in (prog, prog[::-1]):
    Us=[np.linalg.multi_dot([pulse(r,t,c) for r,t in order]) for c in range(3)]
    print("library program matches target:",matches(Us), " cost (quarter-times):", sum(t for _,t in order)/q)

def idx(r):
    r=np.array(r,float)
    for i,x in enumerate(roots):
        if np.allclose(x,r) or np.allclose(x,-r): return i
b=[idx(E[0]-E[2]),idx(E[0]+E[2]),idx(E[1]-E[3]),idx(E[1]+E[3])]
sg=[1,-1,1,-1]
T=[0.5*sum(sg[j]*Rm[b[j]][c] for j in range(4)) for c in range(3)]
G=[Bp[c]@odd[c] for c in range(3)]   # wanted generator
for c in range(3):
    print("class",c,"T = beta on odd:",np.allclose(odd[c]@T[c]@odd[c],G[c]), " T odd-even block zero:",np.allclose(odd[c]@T[c]@even[c],0)," T on even zero:",np.allclose(even[c]@T[c]@even[c],0))
# single-reflection echoes: R T R + T == 2G ?
ok=[i for i in range(12) if all(np.allclose(T[c]+Rm[i][c]@T[c]@Rm[i][c],2*G[c]) for c in range(3))]
print("single-reflection echoes:",[roots[i] for i in ok])
# products of two commuting reflections
ok2=[]
for i in range(12):
    for j in range(i+1,12):
        if all(np.allclose(Rm[i][c]@Rm[j][c],Rm[j][c]@Rm[i][c]) for c in range(3)):
            W=[Rm[i][c]@Rm[j][c] for c in range(3)]
            if all(np.allclose(T[c]+W[c]@T[c]@W[c],2*G[c]) for c in range(3)): ok2.append((roots[i],roots[j]))
print("two-reflection echoes:",ok2)
# any T' = 1/2 sum of +/- reflections (4 distinct) that equals G exactly on all classes (no echo needed)?
sols=[]
for comb in itertools.combinations(range(12),4):
    for s in itertools.product((1,-1),repeat=4):
        Tp=[0.5*sum(s[k]*Rm[comb[k]][c] for k in range(4)) for c in range(3)]
        if all(np.allclose(Tp[c],G[c]) for c in range(3)): sols.append(([roots[i] for i in comb],s))
print("direct 4-reflection generators equal to beta_odd + 0_even:",len(sols))

ph=[idx(E[0]-E[1]),idx(E[0]+E[1]),idx(E[2]-E[3]),idx(E[2]+E[3])]
Q=[np.linalg.multi_dot([pulse(r,3*np.pi/2,c) for r in ph]) for c in range(3)]
Rb=[[Rm[b[j]][c] for c in range(3)] for j in range(4)]
X=[ [Rb[j][c] for c in range(3)] for j in range(4)] + [[Q[c]@Rb[j][c]@Q[c].conj().T for c in range(3)] for j in range(4)]
# include identity (global phase)
X.append([np.eye(8) for c in range(3)])
A=np.array([np.concatenate([x[c].flatten() for c in range(3)]) for x in X]).T
g=np.concatenate([G[c].flatten() for c in range(3)])
sol,res,rk,_=np.linalg.lstsq(A,g,rcond=None)
print("rank",rk,"residual",np.linalg.norm(A@sol-g))
# null space
u,s,vt=np.linalg.svd(A); null=vt[rk:]
print("particular",np.round(sol.real,3)); print("null dims",len(null)); print(np.round(null.real,3))
Xall=[[Rm[k][c] for c in range(3)] for k in range(12)]+[[np.eye(8) for c in range(3)]]
A2=np.array([np.concatenate([x[c].flatten() for c in range(3)]) for x in Xall]).T
sol2=np.linalg.lstsq(A2,g,rcond=None)[0]
print("beta_odd + 0_even in span of the 12 reflections (+1)? residual",np.linalg.norm(A2@sol2-g))
# commutation check of the 24q split: R1,R3 vs Q R2 Q^dag, Q R4 Q^dag
P1=[0.5*(Rb[0][c]+Rb[2][c]) for c in range(3)]; P2=[Q[c]@(-0.5*(Rb[1][c]+Rb[3][c]))@Q[c].conj().T for c in range(3)]
print("halves commute:",all(np.allclose(P1[c]@P2[c],P2[c]@P1[c]) for c in range(3)), " sum = G:",all(np.allclose(P1[c]+P2[c],G[c]) for c in range(3)))
# verify the 24q program
th=np.pi/2
prog=[(b[0],np.pi/2),(b[2],np.pi/2)]
Us=[]
for c in range(3):
    U=pulse(b[0],np.pi/2,c)@pulse(b[2],np.pi/2,c)@Q[c]@pulse(b[1],3*np.pi/2,c)@pulse(b[3],3*np.pi/2,c)@Q[c].conj().T
    Us.append(U)
print("24q program matches certain flip:",matches(Us))
