import numpy as np
G=np.array([[2,0,-1,0,0,0,0,0],[0,2,0,-1,0,0,0,0],[-1,0,2,-1,0,0,0,0],[0,-1,-1,2,-1,0,0,0],
[0,0,0,-1,2,-1,0,0],[0,0,0,0,-1,2,-1,0],[0,0,0,0,0,-1,2,-1],[0,0,0,0,0,0,-1,2]])
cu=np.array([1,0,0,0,0,0,0,0]); cv=np.array([0,-2,-1,1,-1,0,0,0])
def ip(x,y): return int(np.asarray(x)@G@np.asarray(y))
def rd(z): return (ip(z,cu)-2*ip(z,cv))%43
simple=[tuple(int(x) for x in np.eye(8,dtype=int)[i]) for i in range(8)]
roots=set(simple); fr=list(roots)
while fr:
    new=[]
    for r in fr:
        for s in simple:
            t=tuple(int(a-ip(r,s)*b) for a,b in zip(r,s))
            if t not in roots: roots.add(t); new.append(t)
    fr=new
R=sorted(roots); idx={r:i for i,r in enumerate(R)}
RA=np.array(R); P=RA@G@RA.T     # pairing matrix
A_=(-2,-3,-4,-6,-5,-4,-3,-2); B_=(0,0,0,0,0,0,0,1); C_=(0,0,0,0,0,0,1,0); BE_=(0,1,1,2,2,2,1,0)
def key(r): return ((ip(r,A_)+ip(r,C_))%2,(ip(r,A_)+ip(r,BE_))%2)
ST=[idx[x] for x in (A_,B_,C_,BE_)]
Dint=[i for i in range(240) if all(P[i,s]==0 for s in ST)]
# spacetime D4 = roots orthogonal to Dint
Dst=[i for i in range(240) if all(P[i,j]==0 for j in Dint)]
def refl(a): return np.array([idx[tuple(RA[i]-P[i,a]*RA[a])] for i in range(240)])
ar=np.arange(240)
def gen_group(rs):
    gens=[refl(a) for a in rs]; G0={ar.tobytes():ar}; fr=[ar]
    while fr:
        new=[]
        for g in fr:
            for s in gens:
                h=s[g]; k=h.tobytes()
                if k not in G0: G0[k]=h; new.append(h)
        fr=new
    return list(G0.values())
