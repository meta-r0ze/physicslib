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
