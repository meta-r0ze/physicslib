"""Which gauge sector can carry the 16 channels? Persistence-reading elimination (no data).

Readings used (no Standard Model input; every number is library data):
  1. Conservation: the library's channel symmetries (permuteColour, flipWeak) act by
     substrate moves, i.e. reflections in roots of a sector R, and keep all costs (inner
     products). Channels are least-cost lattice vectors: E8 roots.
  2. Hypercharge (PacketGaugeActions.charge: Q 1/3, u 4/3, d -2/3, L -1, nu 0, e -2) is a
     direction y in span(R), orthogonal to the colour and weak roots: pairing gives the charge.
  3. Walls: ProtocolInventory.active is the wall bit (true on the doublets Q, L; false on the
     singlets u, d, nu, e). wallClass puts a generation's channels in the two cosets other than
     its own, so the doublets share one glue coset and the singlets the other.
  4. Economy: least rank, and R contains the internal D4.
Results (2026-11-23):
  * internal D4: fails reading 1 (no weak reflection commutes with colour; SU(3)xSU(2) is not
    in SO(8)). Also tools/placement_d4_nogo.py (corrected: exact stabilizers).
  * D4 + A1 (any spacetime root): passes 1 + 2 together and 1 + 3 together, never 1 + 2 + 3.
  * D5 (all 12): fails 1 + 3 for every colour and weak choice (wall.py below).
So no rank-5 sector meets all four readings. Open: rank 6 (D6, D5+A1, D4+A2, D4+2A1, E6),
or one of the readings is wrong (most likely candidates: y in span(R), or 'active = wall bit'
for every generation).
Run: python3 pm_sector_wall.py d4a1 | d5  (needs pm_sector_base.py beside it)
"""
import itertools, collections, sys
exec(open(__file__.replace('pm_sector_wall.py','pm_sector_base.py')).read())
def d5list():
    seen=[]; 
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
        if len(S)==40 and S not in seen: seen.append(S)
    return seen
KEYS=[(0,1),(1,0),(1,1)]
def run(Rset,name):
    pos=list({min(a,idx[tuple(-RA[a])]) for a in Rset})
    stats=collections.Counter()
    for a,b in itertools.permutations(pos,2):
        if abs(P[a,b])!=1: continue
        for w in pos:
            if P[w,a]!=0 or P[w,b]!=0: continue
            A,B,W=refl(a),refl(b),refl(w)
            fA,fB,fW=A==ar,B==ar,W==ar; fAW=A[W]==ar
            C=[ar,A,B,A[B],B[A],A[B[A]]]
            ky=lambda S:{key(R[int(z)]) for z in S}
            sing=np.where(fA&fB&fW)[0]; Ls=np.where(fA&fB&~fW)[0]
            Us=np.where(fB&fW&~fA)[0]; Qs=np.where(fB&~fA&~fW&~fAW)[0]
            for K1,K2 in itertools.permutations(KEYS,2):
                L1=[l for l in Ls if ky({l,W[l]})=={K1}]
                Q1=[q for q in Qs if ky({g[x] for g in C for x in (q,W[q])})=={K1}]
                S2=[s for s in sing if key(R[s])==K2]
                U2=[u for u in Us if ky({g[u] for g in C})=={K2}]
                t=(len(S2)>=2,bool(L1),len(U2)>=2,bool(Q1)); stats[t]+=1
    ok=stats[(True,True,True,True)]
    print(name,'| wall structure possible in',ok,'of',sum(stats.values()),'(colour,weak,walls) choices', dict(stats) if not ok else '',flush=True)
which=sys.argv[1]
if which=='d4a1':
    done=set()
    for a in Dst:
        m=min(a,idx[tuple(-RA[a])])
        if m in done: continue
        done.add(m); run(Dint+[a,idx[tuple(-RA[a])]],'D4+A1')
if which=='d5':
    for S in d5list():
        r=[x for x in S if x not in Dint][0]
        run(sorted(S),'D5 through coset '+str(key(R[r])))
