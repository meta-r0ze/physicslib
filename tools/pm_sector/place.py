"""Charge-correct mass pairs on the derived sector: root steps of each transition (no data).

Run from tools/pm_sector after generations.py: python3 place.py (writes placement.pkl);
python3 pairs.py.
Electric charge Q = T3 + Y/2 with T3 = +-1/2 from the doublet member's pairing with the weak
root; one sign convention for quarks and leptons. Up pairs use the T3 = +1/2 member, down and
lepton pairs the T3 = -1/2 member, so the transition h = r_right - r_left pairs +3 (up) or -3
(down, lepton) with 3Y: the down = lepton != up orientation follows from charge conservation.
Results (2026-11-23), over all root choices left in the sector:
  * h is colour-blind, and its glue key is the generation's own coset.
  * generations (1,0) and (1,1): up h is one root step (norm 2), down h is two (norm 4), for
    every choice. Leptons: one or two steps, by choice. Generation (0,1): any combination.
  * Compared with TierLedger.tiersFor (down {0,1,2}, up {0,2,3}): up - down = 0, 1, 1. This
    matches if the clock generation (0,1) is tier 0 and one fewer root step gives one more
    power of Delta. Neither rule is derived yet; nor is the lepton choice (declared lepton tiers
    equal down's, i.e. two steps).
"""
exec(open('generations.py').read().split("res=collections.Counter(); example=None")[0])
TYPES={}
by=collections.defaultdict(set)
for a_,b_,w_,K1_,K2_ in PASSES: by[(a_,b_,w_)].add((K1_,K2_))
(a,b,w),walls=next(iter(by.items()))
span=RA[sorted(S)].astype(float); M=np.array([span@G@RA[o] for o in (a,b,w)]+[span@G@t])
_,s_,vt=np.linalg.svd(M); Yb=vt[(s_>1e-9).sum():]@span
pergen=collections.defaultdict(list); wallof={}
for K1,K2 in walls:
    g=[k for k in range(3) if k not in (K1,K2)][0]
    for c,p in placements(a,b,w,K1,K2,Yb): pergen[g].append((c,p,K1,K2))
common=set.intersection(*[{c for c,*_ in pergen[g]} for g in range(3)])
c=sorted(common)[0]
y=np.array(c)@Yb
A,B,W=RT[a],RT[b],RT[w]
gcol=[ar,A,B[A]]
def colour_rep(S):  # element of S fixed by B
    return [z for z in S if B[z]==z][0]
choice={}
for g in range(3):
    opts=[(p,K1,K2) for cc,p,K1,K2 in pergen[g] if cc==c]
    choice[g]=opts
print('options per generation:',{g:len(v) for g,v in choice.items()})
def chan(g,p):
    T=TYPES[p]; out={}
    out['nu']=min(T['nu']); out['e']=min(T['e'])
    q0=colour_rep(T['Q']) if any(B[z]==z for z in T['Q']) else None
    qs=[z for z in T['Q'] if B[z]==z]          # the two weak members of colour 0
    for col in range(3):
        for z in qs: out[('Q',col,int(RA[z]@G@RA[w]))]=int(gcol[col][z])
        out[('u',col)]=int(gcol[col][colour_rep(T['u'])]); out[('d',col)]=int(gcol[col][colour_rep(T['d'])])
    for z in T['L']: out[('L',int(RA[z]@G@RA[w]))]=z
    return out
yv=lambda z:round(float(RA[z]@G@y),6)
for g in range(3):
    p,K1,K2=choice[g][0]; ch=chan(g,p)
    print('gen',KEYS[g],'doublets',KEYS[K1],'singlets',KEYS[K2],'| 3Y:',{k:yv(v) for k,v in ch.items() if not isinstance(k,tuple) or k[1]==0 or k[0]=='L'})
pickle.dump((a,b,w,y,{g:[chan(g,p) for p,_,_ in choice[g]] for g in range(3)},{g:[(K1,K2) for _,K1,K2 in choice[g]] for g in range(3)}),open('placement.pkl','wb'))
