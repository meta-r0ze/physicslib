import itertools, collections, sys, time
exec(open('base.py').read())
RT=np.array([refl(a) for a in range(240)])      # RT[a] = permutation by reflection in root a
neg=np.array([idx[tuple(-RA[i])] for i in range(240)])
RG=(RA@G).astype(float)
KEYS=[(0,1),(1,0),(1,1)]
keyarr=np.array([KEYS.index(key(R[i])) if key(R[i])!=(0,0) else -1 for i in range(240)])
def closure(start):
    S=set(start); fr=list(S)
    while fr:
        n=[]
        for x in fr:
            for y in list(S):
                z=int(RT[y][x])
                if z not in S: S.add(z); n.append(z)
        fr=n
    return frozenset(S)
def rank(S): return np.linalg.matrix_rank(RA[sorted(S)].astype(float))
PASSES=[]
Yc={'nu':0,'e':-6,'L':-3,'u':4,'d':-2,'Q':1}
def test(Rset, y_in_span=True, walls=True, extra_orth=()):
    pos=sorted({min(a,int(neg[a])) for a in Rset})
    span=RA[sorted(Rset)].astype(float)
    res=collections.Counter()
    for a,b in itertools.permutations(pos,2):
        if abs(P[a,b])!=1: continue
        for w in pos:
            if P[w,a] or P[w,b]: continue
            A,B,W=RT[a],RT[b],RT[w]
            fA,fB,fW=A==ar,B==ar,W==ar; fAW=A[W]==ar
            C=[ar,A,B,A[B],B[A],A[B[A]]]
            sing=np.where(fA&fB&fW)[0]; Ls=np.where(fA&fB&~fW)[0]
            Us=np.where(fB&fW&~fA)[0]; Qs=np.where(fB&~fA&~fW&~fAW)[0]
            orbC=lambda x:{int(g[x]) for g in C}
            orbQ=lambda x:orbC(x)|orbC(W[x])
            # y basis: in span(R) (or all of R^8) orthogonal to a,b,w (pairing via G)
            base=span if y_in_span else np.eye(8)
            M=np.array([base@G@RA[o] for o in (a,b,w)]+[base@G@np.asarray(v) for v in extra_orth])
            _,s,vt=np.linalg.svd(M); N=vt[(s>1e-9).sum():]
            Yb=N@base                          # rows: allowed y directions
            if len(Yb)==0: res['no y']+=1; continue
            PV=RG@Yb.T                         # 240 x k pairings with basis
            pairs=[(K1,K2) for K1,K2 in itertools.permutations(range(3),2)] if walls else [(None,None)]
            for K1,K2 in pairs:
                inK=lambda S,K: K is None or all(keyarr[z]==K for z in S)
                L1=[l for l in Ls if inK({int(l),int(W[l])},K1)]
                Q1=[q for q in Qs if inK(orbQ(q),K1)]
                S2=[s for s in sing if inK({int(s)},K2)]
                U2=[u for u in Us if inK(orbC(u),K2)]
                if len(S2)<2 or not L1 or len(U2)<2 or not Q1: res['types/walls fail']+=1; continue
                ok=False
                # charge: find c with PV[x]@c = Y; enumerate e,L,Q reps and solve least squares with nu too
                for nu in S2:
                  for e in S2:
                    if e==nu: continue
                    for l in L1:
                      for q in Q1:
                        Mx=PV[[nu,e,l,q]]; bx=np.array([0,-6,-3,1.])
                        c,*_=np.linalg.lstsq(Mx,bx,rcond=None)
                        if np.abs(Mx@c-bx).max()>1e-6: continue
                        v=np.round(PV@c,6)
                        if any(v[u]==4 for u in U2) and any(v[u]==-2 for u in U2):
                            # free directions left? fine: existence is enough
                            ok=True; break
                      if ok: break
                    if ok: break
                  if ok: break
                res['PASS' if ok else 'charge fails']+=1
                if ok: PASSES.append((a,b,w,K1,K2))
    return res
if __name__=='__main__':
    T=time.time(); mode=sys.argv[1]
    if mode=='d4a1':
        a=Dst[0]; S=closure(Dint+[a])
        for ys,wl in [(True,True),(False,True),(True,False)]:
            print('D4+A1 y_in_span=%s walls=%s'%(ys,wl),dict(test(S,ys,wl)),f'{time.time()-T:.0f}s',flush=True)
