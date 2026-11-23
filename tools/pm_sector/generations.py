"""Gauge sector of the 16 channels by persistence readings, and the three generations in it.

Run order (from this folder): python3 rank6.py  (writes sectors.pkl); python3 generations.py
Readings (library data only): channel symmetries (permuteColour, flipWeak) act by root
reflections of a sector R and keep inner products; channels are E8 roots with each channel's
exact stabilizer; hypercharge (PacketGaugeActions.charge) is the pairing with one direction y in
span(R) orthogonal to the colour and weak roots; walls: doublets (active) in one glue coset,
singlets in another, generation = the third (wallClass); Economy: R contains the internal D4,
least rank, then fewest roots; time: gauge roots and y commute with time translation, i.e.
are orthogonal to the clock time vector t (the unique sum of two orthogonal forward clock-axis
roots; every forward tick pairs 2 with it).
Results (2026-11-23):
  * least rank 6, fewest roots: D4 + 2A1 (18 sectors, all pass without the time reading);
  * time reading: the two extra A1 must be clock-silent (3 sectors), and only one of those
    has a charge direction orthogonal to t: a unique sector. The weak flip is always the same
    one of its two extra roots; the other carries the charge direction.
  * every passing colour/weak choice hosts all three generations with one common charge
    direction. Walls: generation (0,1) [vector, clock coset]: doublets in either spinor coset;
    generations (1,0) and (1,1): doublets in the vector coset (0,1). The library's cyclic
    wallClass (doublets in wall g-1) agrees for g = 0, 1 and disagrees for g = 2.
  * generation (0,1) is disjoint from the other two; generations (1,0) and (1,1) must share
    their quark-doublet roots (6), and nothing else. The library carries the generation in the
    packet coset, so a shared label is allowed.
"""
exec(open('gen.py').read().split("by=collections")[0].replace("print(","(lambda *a,**k:None)("))
def placements(a,b,w,K1,K2,Yb):
    A,B,W=RT[a],RT[b],RT[w]; fA,fB,fW=A==ar,B==ar,W==ar; fAW=A[W]==ar
    C=[ar,A,B,A[B],B[A],A[B[A]]]
    orbC=lambda x:frozenset(int(g[x]) for g in C); orbQ=lambda x:orbC(x)|orbC(W[x])
    inK=lambda S,K: all(keyarr[z]==K for z in S)
    sing=[s for s in np.where(fA&fB&fW)[0] if keyarr[s]==K2]
    Ls={frozenset({int(l),int(W[l])}) for l in np.where(fA&fB&~fW)[0]}; Ls=[x for x in Ls if inK(x,K1)]
    Us={orbC(u) for u in np.where(fB&fW&~fA)[0]}; Us=[x for x in Us if inK(x,K2)]
    Qs={orbQ(q) for q in np.where(fB&~fA&~fW&~fAW)[0]}; Qs=[x for x in Qs if inK(x,K1)]
    PV=RG@Yb.T; out=[]
    for nu in sing:
      for e in sing:
        if e==nu: continue
        for l in Ls:
          for q in Qs:
            rows=[nu,e,min(l),min(q)]; bx=np.array([0,-6,-3,1.])
            c,*_=np.linalg.lstsq(PV[rows],bx,rcond=None)
            if np.abs(PV[rows]@c-bx).max()>1e-6: continue
            v=np.round(PV@c,6)
            if any(v[z]!=-3 for z in l) or any(v[z]!=1 for z in q): continue
            us=[x for x in Us if all(v[z]==4 for z in x)]; ds=[x for x in Us if all(v[z]==-2 for z in x)]
            for u in us:
              for d in ds:
                out.append((tuple(np.round(c,6)),frozenset({nu,e})|l|q|u|d)); TYPES[frozenset({nu,e})|l|q|u|d]={'nu':{nu},'e':{e},'L':set(l),'Q':set(q),'u':set(u),'d':set(d)}
    return out
res=collections.Counter(); example=None; TYPES={}
for (a,b,w),gk in by.items() if False else []: pass
by=collections.defaultdict(set)
for a,b,w,K1,K2 in PASSES: by[(a,b,w)].add((K1,K2))
for (a,b,w),walls in by.items():
    span=RA[sorted(S)].astype(float); M=np.array([span@G@RA[o] for o in (a,b,w)]+[span@G@t])
    _,s_,vt=np.linalg.svd(M); Yb=vt[(s_>1e-9).sum():]@span
    pergen=collections.defaultdict(list)
    for K1,K2 in walls:
        g=[k for k in range(3) if k not in (K1,K2)][0]
        pergen[g]+=placements(a,b,w,K1,K2,Yb)
    ys=[{c for c,_ in pergen[g]} for g in range(3)]
    common=ys[0]&ys[1]&ys[2]
    for c in list(common)[:3]:
        P0=[p for cc,p in pergen[0] if cc==c]; P1=[p for cc,p in pergen[1] if cc==c]; P2=[p for cc,p in pergen[2] if cc==c]
        best=min(((len(x&y),len(x&z),len(y&z),y,z) for x in P0 for y in P1 for z in P2), key=lambda q:q[0]+q[1]+q[2])
        y,z=best[3],best[4]; ty=TYPES[y]; tz=TYPES[z]
        shared=[(k1,k2) for k1 in ty for k2 in tz if ty[k1]&tz[k2]]
        res[('g1/g2 shared types',tuple(shared))]+=1
        best=best[:3]
        res[('overlaps g0g1,g0g2,g1g2 (min)',best)]+=1
print(dict(res)); raise SystemExit
import pickle; pickle.dump(example,open('example.pkl','wb'))
if example:
    a,b,w,c,p0,p1,p2=example; print('example y coefficients',c)
