"""Aligning SliceHop's clock axis with the E8 clock plane (exploration; no data).

SliceHop takes a D4 sector, uses coordinate 3 as the clock axis and the roots with
clock coordinate 0 (the slice, a D3) for within-tick spatial hops; the roots through
the clock axis (+-e_i +- e_3, "clock words") change the clock coordinate by +-1.
The receiver-ring proposal (PMKAutomaton.ClockRing) uses the E8 clock plane:
a root event is one tick when it changes clockReading by +-1.

The library never placed SliceHop's D4 relative to ClockPlane. This script searches
all placements whose slice D3 lies in the clock plane's stabilizer A4 (so spatial
hops are clock-silent) and records the clock readings of the twelve clock words.
It also checks which one-tick orbits the aligned clock words use and that the
orthogonal complement is a D4 (E8 = D4 + D4, PMSubstrate.Channels).
Companion: tools/clock_ring_check.py, tools/clock_stabilizer_orbits.py.
"""
import numpy as np, itertools, collections
G=np.array([[2,0,-1,0,0,0,0,0],[0,2,0,-1,0,0,0,0],[-1,0,2,-1,0,0,0,0],[0,-1,-1,2,-1,0,0,0],
[0,0,0,-1,2,-1,0,0],[0,0,0,0,-1,2,-1,0],[0,0,0,0,0,-1,2,-1],[0,0,0,0,0,0,-1,2]])
cu=np.array([1,0,0,0,0,0,0,0]); cv=np.array([0,-2,-1,1,-1,0,0,0])
ip=lambda a,b:int(np.asarray(a)@G@np.asarray(b))
ph=lambda z:(lambda r: r if r<=21 else r-43)((ip(z,cu)-2*ip(z,cv))%43)
simple=[tuple(int(x) for x in np.eye(8,dtype=int)[i]) for i in range(8)]
roots=set(simple); fr=list(roots)
while fr:
    new=[]
    for r in fr:
        for s in simple:
            t=tuple(int(a-ip(r,s)*b) for a,b in zip(r,s))
            if t not in roots: roots.add(t); new.append(t)
    fr=new
roots=sorted(roots)
A4=[r for r in roots if ip(r,cu)==0 and ip(r,cv)==0]
def closure(gens):
    S=set(gens)|{tuple(-x for x in g) for g in gens}; fr=list(S)
    while fr:
        new=[]
        for r in fr:
            for g in gens:
                t=tuple(int(a-ip(r,g)*b) for a,b in zip(r,g))
                if t not in S: S.add(t); new.append(t)
        fr=new
    return S
# all A3 paths (a,b,c) in A4: <a,b>=-1,<b,c>=-1,<a,c>=0
results=collections.Counter(); examples={}
for a,b,c in itertools.permutations(A4,3):
    if ip(a,b)!=-1 or ip(b,c)!=-1 or ip(a,c)!=0: continue
    D3=closure([a,b,c])
    if len(D3)!=12: continue
    for beta in roots:
        if ip(beta,b)!=1 or ip(beta,a)!=0 or ip(beta,c)!=0: continue
        D4=closure([a,b,c,beta])
        if len(D4)!=24: continue
        clockw=[r for r in D4 if r not in D3]
        key=tuple(sorted(collections.Counter(ph(r) for r in clockw).items()))
        results[key]+=1; examples.setdefault(key,(a,b,c,beta))
for k,v in results.most_common(): print(v,"placements; clock-word readings:",dict(k))
key=[k for k in results if dict(k)=={-1:6,1:6}][0]
a,b,c,beta=examples[key]
D3=closure([a,b,c]); D4=closure([a,b,c,beta])
print("slice roots all clock-silent:", all(ph(r)==0 for r in D3))
print("slice roots orthogonal to the clock plane:", all(ip(r,cu)==0 and ip(r,cv)==0 for r in D3))
plusD4=[r for r in D4 if r not in D3 and ph(r)==1]
cls=lambda r:(ip(r,cu),ip(r,cv))
print("+1 clock words by projection class:",dict(collections.Counter(cls(r) for r in plusD4)))
singles={r for r in roots if ph(r)==1 and all(ip(r,x)==0 for x in A4)}
print("+1 clock words that are A4-fixed singletons:",sum(r in singles for r in plusD4))
# check: across all 960 aligned placements, how many +1 clock words are singletons / class (1,0)
stats=collections.Counter()
for x,y,z in itertools.permutations(A4,3):
    if ip(x,y)!=-1 or ip(y,z)!=-1 or ip(x,z)!=0: continue
    d3=closure([x,y,z])
    if len(d3)!=12: continue
    for bt in roots:
        if ip(bt,y)!=1 or ip(bt,x)!=0 or ip(bt,z)!=0: continue
        d4=closure([x,y,z,bt])
        if len(d4)!=24: continue
        cw=[r for r in d4 if r not in d3]
        if sorted(ph(r) for r in cw)!=[-1]*6+[1]*6: continue
        p=[r for r in cw if ph(r)==1]
        stats[(sum(r in singles for r in p), tuple(sorted(collections.Counter(cls(r) for r in p).items())))]+=1
print("aligned placements by (#singletons among +1 clock words, class split):",dict(stats))
comp=[r for r in roots if all(ip(r,x)==0 for x in D4)]
print("roots orthogonal to the aligned D4:",len(comp), "closure size:",len(closure(comp)) if comp else 0)
print("clock-silent roots in the complement:",sum(ph(r)==0 for r in comp),
      " readings there:",dict(collections.Counter(ph(r) for r in comp)))
