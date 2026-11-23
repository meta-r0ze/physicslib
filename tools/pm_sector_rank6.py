"""Gauge sector for the 16 channels by persistence elimination, rank 5 and rank 6 (no data).

Readings (library data only): (1) permuteColour and flipWeak act by reflections in roots of a
sector R and keep all inner products; channels are E8 roots with each channel's exact
stabilizer. (2) Hypercharge (PacketGaugeActions.charge) is the pairing with one direction y
orthogonal to the colour and weak roots. (3) Walls: doublets (active) share one glue coset and
singlets the other (wallClass). (4) Economy: R contains the internal D4; least rank; then the
fewest roots.
Results (2026-11-23):
  rank 5: D4+A1 passes (1)+(3), and passes (1)+(2)+(3) only if y may leave span(R). With y in
          span(R) it fails: colour (2 directions) + weak (1) leave no room for a separate charge
          direction that respects the walls. D5 fails (1)+(3). So hypercharge needs its own
          direction: rank 6.
  rank 6 (140 sectors containing the internal D4): D4+2A1 (28 roots, 18 sectors), D4+A2 (30),
          D5+A1 (42), D6 (60) pass (one instance each tested); E6 (72) failed in the instance
          tested. All 18 D4+2A1 pass.
  Economy (fewest roots) selects D4+2A1: the internal D4 and two orthogonal spacetime A1, one
  for the weak flip, one carrying the charge direction. The 18 differ only by the clock: both
  extra roots clock-silent (3), one silent and one clock-axis (12), both clock-axis (3).
Run: python3 pm_sector_rank6.py rank5 | rank6 | d42a1   (needs pm_sector_base.py beside it)
"""
import itertools, collections, sys, time
exec(open(__file__.replace('pm_sector_rank6.py','pm_sector_base.py')).read())
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
Yc={'nu':0,'e':-6,'L':-3,'u':4,'d':-2,'Q':1}
def test(Rset, y_in_span=True, walls=True):
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
            M=np.array([base@G@RA[o] for o in (a,b,w)])
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
    return res
if __name__=='__main__':
    mode=sys.argv[1]
    extra=[i for i in range(240) if i not in Dint]
    S5={closure(Dint+[r]) for r in extra}; S5={s for s in S5 if rank(s)==5}
    if mode=='rank5':
        for S in sorted(S5,key=sorted)[:2]:
            for ys,wl in [(True,True),(False,True),(True,False)]:
                print(len(S),'roots, y_in_span=%s walls=%s'%(ys,wl),dict(test(S,ys,wl)),flush=True)
    else:
        S6=set()
        for S in S5:
            for r in extra:
                if r not in S:
                    X=closure(list(S)+[r])
                    if rank(X)==6: S6.add(X)
        names={28:'D4+2A1',30:'D4+A2',42:'D5+A1',60:'D6',72:'E6'}
        by=collections.defaultdict(list)
        for s in sorted(S6,key=sorted): by[len(s)].append(s)
        if mode=='rank6':
            for n in sorted(by): print(names[n],len(by[n]),'sectors; first:',dict(test(by[n][0],True,True)),flush=True)
        if mode=='d42a1':
            for i,S in enumerate(by[28]):
                ext=sorted({min(a,int(neg[a])) for a in S if a not in Dint})
                print(i,[(lambda x:x if x<=21 else x-43)(rd(R[a])) for a in ext],dict(test(S,True,True)),flush=True)
