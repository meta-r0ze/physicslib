#!/usr/bin/env python3
"""Cheap structural tests for protocol-register candidates (PMAction REVIEW, Colour register).
T2: orbits of the reference stabilizer W(D3) (fixing +2e0) on each class's even labels.
T5: root moves (b,c) -> (b+a,c+a) that keep a generation's two classes nontrivial."""
import itertools, numpy as np
def cls(v):
    if all(x%2==0 for x in v): return 0
    return 1 if sum(1 for x in v if x<0)%2==0 else 2
V=[tuple(2*s if i==j else 0 for j in range(4)) for i in range(4) for s in (1,-1)]
S=list(itertools.product((1,-1),repeat=4))
C={0:V,1:[v for v in S if cls(v)==1],2:[v for v in S if cls(v)==2]}
# W(D4) stabilizer of the reference carrier +2e0: permutations and even sign changes of axes 1..3
# (signed perms of axes 1,2,3 with an even number of sign flips over all four axes, axis 0 fixed)
stab=[]
for p in itertools.permutations([1,2,3]):
    for sg in itertools.product((1,-1),repeat=3):
        if np.prod(sg)==1:
            stab.append((p,sg))
def act(g,x):
    p,sg=g; y=[x[0],0,0,0]
    for k,ax in enumerate((1,2,3)): y[p[k]]=sg[k]*x[ax]
    return tuple(y)
print("T2: orbits of the reference stabilizer W(D3) on even labels (antipodal pairs) per class")
for c in range(3):
    pairs=[]
    for x in C[c]:
        k=frozenset([x,tuple(-t for t in x)])
        if k not in pairs: pairs.append(k)
    seen=set(); orbits=[]
    for P in pairs:
        if P in seen: continue
        orb=set()
        for g in stab:
            x=next(iter(P)); y=act(g,x); orb.add(frozenset([y,tuple(-t for t in y)]))
        seen|=orb; orbits.append(len(orb))
    print("  class",c,"orbit sizes",orbits)
print("T5: root moves (b,c)->(b+a,c+a) keeping both classes nontrivial, per generation")
add=lambda a,b: a^b   # Z2xZ2 with classes v=1,s=2,c=3 (0 = trivial)
for m in (1,2,3):
    b,c=[x for x in (1,2,3) if x!=m]
    ok=[a for a in (1,2,3) if add(b,a)!=0 and add(c,a)!=0]
    print("  label",m,"classes",(b,c),"admissible a:",ok,"->",[(add(b,a),add(c,a)) for a in ok])
