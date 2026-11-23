"""Tier count from (generation, label): what the packet data can give (exploration; no data).

Question: can the leading mass power Delta^n (tier n) of a program be read from its
generation coset and its label vector (EPLabelGen.channelE8Gen)? Test target, before any
mass: the declared tier sets TierLedger.tiersFor (leptons and down {0,1,2}, up {0,2,3}).

Findings (2026-11-23):
1. Every channel vector is a norm-4 vector of the internal D4 (pairing 0 with the spacetime
   simple roots a, b, c, beta). Triality permutes the same 16 vectors; generations differ only
   in which channel gets which vector.
2. Every root of every glue coset pairs +-1 with every channel vector (32 / 32). The split of
   the coset's silent and one-tick roots by that pairing depends on the generation only, not
   on the label (output below). So no count of coset roots against the label separates
   classes: such a count gives up-type and down-type the same tiers.
3. The only datum that depends on both generation and label is the label's clock reading
   (Z_43). It is a phase inside one period, not a count of periods. It also depends on
   colour (class 1, g=0: -13, 11, -1), and up-type readings are the negatives of down-type
   readings. A tier must be colour-blind, and a sign-blind rule gives up = down.
Conclusion: a single program's (generation, label) data cannot produce the declared up-type
tier set {0,2,3} next to down-type {0,1,2}. Either the up-type tier needs data outside one
program (a weak partner or a composite), or the declared up tier set is a premise to review.
"""
import numpy as np, collections, itertools
G=np.array([[2,0,-1,0,0,0,0,0],[0,2,0,-1,0,0,0,0],[-1,0,2,-1,0,0,0,0],[0,-1,-1,2,-1,0,0,0],
[0,0,0,-1,2,-1,0,0],[0,0,0,0,-1,2,-1,0],[0,0,0,0,0,-1,2,-1],[0,0,0,0,0,0,-1,2]])
cu=np.array([1,0,0,0,0,0,0,0]); cv=np.array([0,-2,-1,1,-1,0,0,0])
ip=lambda x,y:int(np.asarray(x)@G@np.asarray(y))
rd=lambda z:(ip(z,cu)-2*ip(z,cv))%43
simple=[tuple(int(x) for x in np.eye(8,dtype=int)[i]) for i in range(8)]
roots=set(simple); fr=list(roots)
while fr:
    new=[]
    for r in fr:
        for s in simple:
            t=tuple(int(a-ip(r,s)*b) for a,b in zip(r,s))
            if t not in roots: roots.add(t); new.append(t)
    fr=new
roots=sorted(roots); assert len(roots)==240
A=(-2,-3,-4,-6,-5,-4,-3,-2); B=(0,0,0,0,0,0,0,1); C=(0,0,0,0,0,0,1,0); BE=(0,1,1,2,2,2,1,0)
key=lambda r:((ip(r,A)+ip(r,C))%2,(ip(r,A)+ip(r,BE))%2)
x=(-2,-3,-4,-6,-5,-3,-2,-1); print('check',key(x),rd(x),'expect (1,1) 41')
keyOf={0:(0,1),1:(1,0),2:(1,1)}
for g in range(3):
    co=[r for r in roots if key(r)==keyOf[g]]
    c=collections.Counter(min(rd(r),43-rd(r)) if rd(r) else 0 for r in co)
    print(g,len(co),sorted(c.items()))
# channel vectors from Lean (EPLabelGen.channelE8Gen), classes: 1,2 colour-triplet singlets, 3 colourless doublet, 5 charged singlet
V={0:{1:(0,0,1,2,1,0,0,0),2:(0,0,-1,-2,-1,0,0,0),3:(0,-1,1,0,0,0,0,0),5:(0,2,1,2,1,0,0,0)},
   1:{1:(0,-1,-1,0,0,0,0,0),2:(0,1,1,0,0,0,0,0),3:(0,-1,0,0,1,0,0,0),5:(0,1,-1,0,0,0,0,0)},
   2:{1:(0,-1,0,0,-1,0,0,0),2:(0,1,0,0,1,0,0,0),3:(0,-2,-1,-2,-1,0,0,0),5:(0,1,0,0,-1,0,0,0)}}
for k in (5,3,1,2):
  print('class',k)
  for g in range(3):
    v=V[g][k]; co=[r for r in roots if key(r)==keyOf[g]]
    sil=[r for r in co if rd(r)==0]; one=[r for r in co if rd(r) in (1,42)]
    f=lambda S:collections.Counter(ip(r,v) for r in S)
    print(' g',g,'read',rd(v),'all',dict(sorted(f(co).items())),'silent',dict(sorted(f(sil).items())),'tick',dict(sorted(f(one).items())))
