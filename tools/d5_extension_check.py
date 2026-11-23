"""D5 extensions of the internal D4 inside E8 (exploration; no data).

Every one of the 192 glue-coset roots extends the internal D4 to a D5 (40 roots). There are
12 distinct D5, 4 in each glue coset; each adds one direction d (norm 4, in the spacetime D4
weight space) and its 16 roots +-e_i +- e5 lie in one coset. E8 then splits as D5 + A3 with
the A3 inside the spacetime D4.
Clock reading of d (2026-11-23): vector coset (0,1): 0, 0, 0, 2; coset (1,0): -1, 1, 1, 1;
coset (1,1): 1, -1, 1, -1. Only the vector (clock) coset has D5 whose extra direction is
clock-silent, and it has three. The internal D4 roots themselves are not clock-silent.
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
import collections
ST=[A,B,C,BE]
def closure(gens):
    S=set(gens)|{tuple(-x for x in g) for g in gens}; fr=list(S)
    while fr:
        new=[]
        for r in fr:
            for g in list(S):
                if ip(r,g)==-1:
                    t=tuple(a+b for a,b in zip(r,g))
                    if t not in S and ip(t,t)==2: S.add(t); new.append(t)
        fr=new
    return S
Dst=closure(ST); print('spacetime D4 roots',len(Dst))
Dint=[r for r in roots if all(ip(r,x)==0 for x in Dst)]; print('internal D4 roots',len(Dint))
# simple roots of internal D4: pick via closure check
coset=[r for r in roots if r not in Dst and r not in Dint]
res=collections.Counter(); ex={}
for r in coset:
    S=closure(Dint+[r])
    k=(len(S),key(r),rd(r) if rd(r)<=21 else rd(r)-43)
    res[k]+=1; ex.setdefault(len(S),(r,S))
for k,v in sorted(res.items()): print('closure size, glueKey, reading:',k,'count',v)
print('---- distinct D5s')
seen={}
for r in coset:
    S=frozenset(closure(Dint+[r]))
    if S in seen: continue
    extra=[x for x in S if x not in Dint]
    # 2e5 = (e_i+e5)+(-e_i+e5): find pair in extra summing to a vector orthogonal to internal D4
    two=None
    for x in extra:
        for y in extra:
            s=tuple(a+b for a,b in zip(x,y))
            if any(s) and all(ip(s,d)==0 for d in Dint): two=s; break
        if two: break
    seen[S]=two
for S,two in seen.items():
    e=[r for r in S if r not in Dint]
    keys=collections.Counter(key(r) for r in e)
    inDst=two in Dst or tuple(x//2 for x in two) in Dst
    print('2e5 norm',ip(two,two),'reading',rd(two) if rd(two)<=21 else rd(two)-43,'coset of extra roots',dict(keys),
          'e5-direction pairs with spacetime simple roots',[ip(two,x) for x in ST])
print('---- clock readings of all 40 roots per D5')
print('internal D4 readings',collections.Counter(rd(r) for r in Dint))
for S,two in seen.items():
    c=collections.Counter((rd(r) if rd(r)<=21 else rd(r)-43) for r in S)
    print('d reading',rd(two) if rd(two)<=21 else rd(two)-43,'key',key([r for r in S if r not in Dint][0]),'root readings',dict(sorted(c.items())))
