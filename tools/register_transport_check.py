#!/usr/bin/env python3
"""Second register brainstorm (PMElementaryParticles REVIEW, "Protocol register and coupling").
Tests: T1 32 light components per generation; T2 a 1+3 label split about the reference axis;
T3 a doublet sign; T4 label unchanged by wall terms (Map); T6 label moved by the particle's
transport (Protocol); T7 label separate from the Dirac generators (ColourRegister).
Light Dirac components per label: 2 zero modes per wall x 2 walls = 4."""
import itertools

light = 4
print("T1 counts:")
for name, labels in [("even modes of the other wall", 4), ("vector carriers: axis x sign", 8),
                     ("16 channels incl. hand (double counts the walls)", 16)]:
    print(f"  {name}: {labels} x {light} = {labels * light} (need 32)")

print("Idea: label = auxiliary axis k of the hop's root pair (2e_j = (e_j+e_k)+(e_j-e_k))")
for k in range(4):
    use = [j for j in (1, 2, 3) if j != k]
    print(f"  k={k}: serves spatial directions {use}; in the clock slice: {use if k else []}")

print("Idea: E8 glued roots = generation x protocol x wire carrier")
pure, glued = 2 * 24, 3 * 64
print(f"  E8 roots = {pure} pure (D4+D4 roots) + {glued} glued (classes v,s,c: 8 x 8 each) = {pure + glued}")
print(f"  per glue class: 8 protocol carriers (D4_1) x 8 wire carriers (D4_2) = 64; three classes = three generations")

print("Third wall placement: walls = the two D4 factors of one glue class")
import itertools
import numpy as np
h=0.5
V=[tuple(s*(i==j) for j in range(4)) for i in range(4) for s in (1,-1)]
S=[p for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==0]
C=[p for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==1]
D4=[tuple(v) for v in set(tuple(np.array(V[a])+np.array(V[b])) for a in range(8) for b in range(8)) if sum(x*x for x in v)==2]
assert len(D4)==24
cls={'v':V,'s':S,'c':C}
roots=set([r+(0,)*4 for r in D4]+[(0,)*4+r for r in D4]+[a+b for k in cls for a in cls[k] for b in cls[k]])
print("  E8 roots", len(roots))
# swap of factors preserves root set
print("  factor swap is a root automorphism:", {r[4:]+r[:4] for r in roots}==roots)
def refl(r,w):
    r=np.array(r);w=np.array(w);return tuple(w-(w@r)*r)  # |r|^2=2
for k,X in cls.items():
    idx={w:i for i,w in enumerate(X)}
    P=np.zeros((8,8))
    for w in X: P[idx[tuple(-np.array(w))],idx[w]]=1
    # D4_1 Weyl reflections act on a, keep class, commute with antipode
    ok=all(tuple(refl(r,w)) in idx for r in D4 for w in X)
    W=[np.array([[1.0 if refl(r,X[j])==X[i] else 0 for j in range(8)] for i in range(8)]) for r in D4]
    comm=all(np.allclose(w@P,P@w) for w in W)
    odd=(np.eye(8)-P)/2; even=(np.eye(8)+P)/2
    T=np.kron(odd,even); F=np.kron(even,odd)
    sw=np.zeros((64,64))
    for i in range(8):
        for j in range(8): sw[j*8+i,i*8+j]=1
    print(" ", k,"refl keeps class",ok,"commute antipode",comm,
          "dim T,F",round(np.trace(T)),round(np.trace(F)),"T.F=0",np.allclose(T@F,0),
          "swap T->F",np.allclose(sw@T@sw.T,F),
          "D4_1 words keep T",all(np.allclose(np.kron(w,np.eye(8))@T,T@np.kron(w,np.eye(8))) for w in W))

print("Candidate: each wall is a glue class read through one D4 factor (amplitude) with the other factor as label")
import itertools, numpy as np
h=0.5
V=[tuple(float(s*(i==j)) for j in range(4)) for i in range(4) for s in (1,-1)]
S=[p for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==0]
C=[p for p in itertools.product((h,-h),repeat=4) if sum(x<0 for x in p)%2==1]
cls=[V,S,C]   # class index 0,1,2
D4=[r for r in {tuple(np.array(a)+np.array(b)) for a in V for b in V} if sum(x*x for x in r)==2]
def key(w): return tuple(round(x,6)+0.0 for x in w)
cof={key(w):k for k in range(3) for w in cls[k]}
roots={key(r+(0.,)*4) for r in D4}|{key((0.,)*4+r) for r in D4}|{key(a+b) for k in range(3) for a in cls[k] for b in cls[k]}
print("E8 roots", len(roots))
# find an order-3 orthogonal map cycling the classes v->s->c->v
H=np.ones((4,4))/2; H[1,2:]*=-1; H[2,1::2]*=-1; H[3,1:3]*=-1
F=np.diag([1,1,1,-1.])
cands=[H@F, F@H]
tau=None
for T in cands:
    img=[{cof.get(key(T@np.array(w))) for w in cls[k]} for k in range(3)]
    if all(len(s)==1 for s in img):
        perm=[s.pop() for s in img]
        if perm==[1,2,0]: tau=T
print("triality found:", tau is not None, " D4 roots kept:", {key(tau@np.array(r)) for r in D4}=={key(r) for r in D4})
def act(M1,M2,r): r=np.array(r); return key(np.concatenate([M1@r[:4],M2@r[4:]]))
print("diagonal triality is an E8 automorphism:", {act(tau,tau,r) for r in roots}==roots)
I=np.eye(4)
print("factor swap is an E8 automorphism:", {key(r[4:]+r[:4]) for r in roots}==roots)
# sectors: glue class x has basis (a,b), a,b in cls[x]
def basis(x): return [key(a+b) for a in cls[x] for b in cls[x]]
anti=lambda w: key(-np.array(w))
def proj(x, odd_first):
    # projector onto odd(a) (x) all(b)  [wall T]  or all(a) (x) odd(b)  [wall F], in class x
    B=basis(x); idx={b:i for i,b in enumerate(B)}; P=np.zeros((64,64))
    for b in B:
        a_,b_=b[:4],b[4:]
        img=idx[key(anti(a_)+b_)] if odd_first else idx[key(a_+anti(b_))]
        P[idx[b],idx[b]]+=0.5; P[img,idx[b]]-=0.5
    return P,idx
for g in range(3):
    x,y=(g+1)%3,(g-1)%3
    PT,iT=proj(x,True); PF,iF=proj(y,False)
    # crossing C = swap then diagonal triality: maps class x -> class y?
    Cm=np.zeros((64,64)); ok=True
    for b,i in iT.items():
        img=act(tau,tau,b[4:]+b[:4])
        if img not in iF: ok=False; break
        Cm[iF[img],i]=1
    print(f"gen {g}: wall T class {x} dim {round(np.trace(PT))}, wall F class {y} dim {round(np.trace(PF))};",
          "crossing lands in class y:",ok, "maps wall T onto wall F:", ok and np.allclose(Cm@PT@Cm.T,PF))
    # a single-wall step on wall T (D4_1 reflection) keeps class x and the label b
    keep=all(key(np.concatenate([np.array(b[:4])-(np.array(b[:4])@np.array(r))*np.array(r),b[4:]])) in iT for r in D4 for b in iT)
    print("   wall-T step keeps class and label:",keep)
