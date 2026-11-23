"""Hypercharge + walls test for D4+A1 and D5; see pm_sector_wall.py for the readings and results."""
import itertools, collections, sys
from fractions import Fraction as Fr
exec(open(__file__.replace('pm_sector_charge.py','pm_sector_base.py')).read())
import numpy as np
def nullspace_in_span(Rset, orth):
    B=RA[Rset].astype(float)            # span of R
    # find coefficients c with (c B) G orth_k = 0
    M=np.array([[float(ip(RA[r],RA[o])) for r in Rset] for o in orth])
    u,s,vt=np.linalg.svd(M); rank=(s>1e-9).sum(); N=vt[rank:]
    Y=N@B                                # vectors in span R orthogonal to orth
    # reduce to independent
    u2,s2,vt2=np.linalg.svd(Y); r2=(s2>1e-9).sum()
    return vt2[:r2]*1.0                  # basis rows (in coordinate space)
Ychan={'nu':0,'e':-6,'L':-3,'u':4,'d':-2,'Q':1}   # 3Y
def run(Rset,name):
    pos=list({min(a,idx[tuple(-RA[a])]) for a in Rset})
    stats=collections.Counter(); found=None
    for a,b in itertools.permutations(pos,2):
        if abs(P[a,b])!=1: continue
        for w in pos:
            if P[w,a]!=0 or P[w,b]!=0: continue
            A,B,W=refl(a),refl(b),refl(w)
            fA,fB,fW=A==ar,B==ar,W==ar; fAW=A[W]==ar
            sing=np.where(fA&fB&fW)[0]; Ls=np.where(fA&fB&~fW)[0]
            Us=np.where(fB&fW&~fA)[0]; Qs=np.where(fB&~fA&~fW&~fAW)[0]
            if len(sing)<2 or len(Ls)==0 or len(Us)<2 or len(Qs)==0: stats['orbit types missing']+=1; continue
            Yb=nullspace_in_span(Rset,[a,b,w])
            pv=lambda r:np.array([RA[r]@G@y for y in Yb])
            dirs=[]
            for nu in sing:
                v=pv(nu)
                if np.linalg.norm(v)>1e-9: dirs.append((np.array([-v[1],v[0]]) if len(v)==2 else None, nu))
                else:
                    stats['free-direction nu']+=1
                    for e in sing:
                        for l in Ls:
                            w2=pv(e)-2*pv(l)
                            if e!=nu and np.linalg.norm(w2)>1e-9: dirs.append((np.array([-w2[1],w2[0]]),nu))
            RG=RA@G
            _u={}
            for d,nu in dirs:
                if d is None: continue
                dn=d/np.linalg.norm(d); dn=dn if (dn[0]>1e-9 or (abs(dn[0])<1e-9 and dn[1]>0)) else -dn
                _u.setdefault((round(dn[0],6),round(dn[1],6),int(nu)),(d,nu))
            dirs=list(_u.values())
            Lm=np.zeros(240,bool); Lm[Ls]=True; Um=np.zeros(240,bool); Um[Us]=True; Qm=np.zeros(240,bool); Qm[Qs]=True
            for d,nu in dirs:
                if d is None: continue
                vals=RG@(d@Yb)
                for e in sing:
                    if e==nu or abs(vals[e])<1e-9: continue
                    v=np.round(vals*(-6/vals[e]),6)
                    t=(bool((Lm&(v==-3)).any()),bool((Um&(v==4)).any()),bool((Um&(v==-2)).any()),bool((Qm&(v==1)).any()))
                    if not all(t): continue
                    stats['gauge+charge ok']+=1
                    grpL=lambda x:{int(x),int(W[x])}
                    grpC=lambda x:{int(g[x]) for g in (ar,A,B,A[B],B[A],A[B[A]])}
                    orbQ=lambda x:set().union(*[grpL(z) for z in grpC(x)])
                    ky=lambda S:{key(R[z]) for z in S}
                    for l in np.where(Lm&(v==-3))[0]:
                      for q in np.where(Qm&(v==1))[0]:
                        Kd=ky(grpL(l))|ky(orbQ(q))
                        if len(Kd)!=1 or (0,0) in Kd: continue
                        for u in np.where(Um&(v==4))[0]:
                          for dd in np.where(Um&(v==-2))[0]:
                            Ks=ky({nu,e})|ky(grpC(u))|ky(grpC(dd))
                            if len(Ks)==1 and Ks!=Kd and (0,0) not in Ks:
                                stats['wall structure ok']+=1
                                if found is None: found=(Kd,Ks)
    print(name,dict(stats),'| complete placement with hypercharge:',found is not None,flush=True)
    return found
which=sys.argv[1]
if which=='d4a1':
    for a in Dst:
        if a<idx[tuple(-RA[a])]: run(Dint+[a,idx[tuple(-RA[a])]],'internal D4 + A1 (spacetime root %d)'%a)
if which=='d5':
    seen=set()
    for r in range(240):
        if r in Dint or r in Dst: continue
        S=set(Dint)|{r}; fr=[r]
        while fr:
            n=[]
            for x in fr:
                for y in list(S):
                    z=int(refl(y)[x])
                    if z not in S: S.add(z); n.append(z)
            fr=n
        S=frozenset(S)
        if len(S)!=40 or S in seen: continue
        seen.add(S); run(sorted(S),'D5 through coset '+str(key(R[r])))
