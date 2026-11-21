"""Generation cosets under the clock (exploration; no data).

With the spacetime D4 aligned to the E8 clock plane (tools/clock_slice_alignment.py),
E8 = D4(spacetime) + D4(internal) + three glue cosets of 64 roots each. The glue
classes are the generations (PMElementaryParticles/OVERVIEW.md#generations-on-the-e8-wire: the three nontrivial D4 glue
classes, related by triality). Exact triality would make the three cosets identical.

This script classifies the 240 roots by coset for every distinct aligned placement and
counts, per coset, the roots that advance the clock reading by +1, by -1, and the
clock-silent roots. The aligned clock breaks triality: the three cosets have distinct
signatures, the same in every aligned placement. Labels A/B/C are by signature; their
match to the library's glue address g (HeavyFlipControl.direct) is not made here.
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
import itertools, collections, numpy as np
def aligned_placements(limit=None):
    out=[]
    for a,b,c in itertools.permutations(A4,3):
        if ip(a,b)!=-1 or ip(b,c)!=-1 or ip(a,c)!=0: continue
        D3=closure([a,b,c])
        if len(D3)!=12: continue
        for beta in roots:
            if ip(beta,b)!=1 or ip(beta,a)!=0 or ip(beta,c)!=0: continue
            D4=closure([a,b,c,beta])
            if len(D4)!=24: continue
            cw=[r for r in D4 if r not in D3]
            if sorted(ph(r) for r in cw)==[-1]*6+[1]*6:
                out.append((frozenset(D3),frozenset(D4)))
    return out
pl=list(dict.fromkeys(aligned_placements()))
print("distinct aligned (D3,D4) placements:",len(pl))
def analyse(D3,D4):
    D4=list(D4); simp=None
    Dint=[r for r in roots if all(ip(r,x)==0 for x in D4)]
    rest=[r for r in roots if r not in D4 and r not in Dint]
    # coset classes: r ~ r' iff r - r' in span_Z(D4 u Dint)
    B=np.array(list(D4)+list(Dint),dtype=float).T   # 8 x 48 generating set
    # lattice basis via integer check: use simple-root sets of each D4
    def basis(sys):
        # pick 4 independent roots generating the lattice: greedy via determinant of Gram
        best=None
        for comb in itertools.combinations(sys,4):
            M=np.array([[ip(x,y) for y in comb] for x in comb])
            if round(abs(np.linalg.det(M)))==4: return list(comb)
    Bas=basis(D4)+basis(list(Dint))
    Bm=np.array(Bas,dtype=float).T
    inv=np.linalg.inv(Bm)
    def same(r,s):
        coef=inv@(np.array(r)-np.array(s)); return np.allclose(coef,np.round(coef))
    classes=[]
    for r in rest:
        for cl in classes:
            if same(r,cl[0]): cl.append(r); break
        else: classes.append([r])
    res=[]
    for cl in classes:
        cnt=collections.Counter(ph(r) for r in cl)
        res.append((len(cl),cnt[1],cnt[-1],cnt[0]))
    return sorted(res,key=lambda x:(-x[1],x)), len(Dint)
seen=collections.Counter()
for D3,D4 in pl:
    res,nint=analyse(D3,D4)
    seen[(nint,tuple(res))]+=1
for k,v in seen.items(): print(v,"placements: internal roots",k[0],"; cosets (size, #+1, #-1, #silent):",k[1])

# account for every one-tick and silent root
D3,D4=pl[0]
Dint=[r for r in roots if all(ip(r,x)==0 for x in D4)]
print("one-tick (+1) roots: spacetime D4", sum(ph(r)==1 for r in D4),
      "internal D4", sum(ph(r)==1 for r in Dint))
print("silent roots: spacetime D4", sum(ph(r)==0 for r in D4),
      "internal D4", sum(ph(r)==0 for r in Dint))

# Which coset is the spacetime-vector class? Use the clock-axis vector 2e3 = f + f',
# f, f' forward clock-axis roots with <f,f'> = 0 (the pair +-e_i + e3).
fwd=[r for r in D4 if r not in D3 and ph(r)==1]
f,fp=next((x,y) for x in fwd for y in fwd if x!=y and ip(x,y)==0)
axis=tuple(a+b for a,b in zip(f,fp))
print("clock-axis vector norm (expect 4):", ip(axis,axis), " reading (expect 2):", ph(axis))
D4l=list(D4); rest=[r for r in roots if r not in D4 and r not in Dint]
Bas=None
for comb in itertools.combinations(D4l,4):
    M=np.array([[ip(x,y) for y in comb] for x in comb])
    if round(abs(np.linalg.det(M)))==4: Bas=list(comb); break
for comb in itertools.combinations(Dint,4):
    M=np.array([[ip(x,y) for y in comb] for x in comb])
    if round(abs(np.linalg.det(M)))==4: Bas+=list(comb); break
inv=np.linalg.inv(np.array(Bas,dtype=float).T)
classes=[]
for r in rest:
    for cl in classes:
        c=inv@(np.array(r)-np.array(cl[0]))
        if np.allclose(c,np.round(c)): cl.append(r); break
    else: classes.append([r])
for cl in classes:
    cnt=collections.Counter(ph(r) for r in cl)
    comp=collections.Counter(ip(r,axis) for r in cl)
    kind="vector (clock-axis components 0,+-1)" if set(comp)<= {0,2,-2} else "spinor (components +-1/2)"
    print(f"coset +1:{cnt[1]} -1:{cnt[-1]} silent:{cnt[0]}  <r,2e3> counts {dict(comp)} -> {kind}")

# Which coset carries the clock? Check +-cu and the roots of the clock's own A4.
cu_t=tuple(int(x) for x in cu)
A4clock=[r for r in roots if all(ip(r,x)==0 for x in A4)]
for cl in classes:
    cnt=collections.Counter(ph(r) for r in cl)
    print(f"coset +1:{cnt[1]} silent:{cnt[0]}  contains cu: {cu_t in cl}  contains -cu: "
          f"{tuple(-x for x in cu_t) in cl}  roots of the clock's A4: {sum(r in A4clock for r in cl)}")
