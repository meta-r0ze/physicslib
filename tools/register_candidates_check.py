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

# Survivor (a): the doublet as the two wall orientations. Orientation 2 runs the cycle the other way
# (P -> P^T). Derived wire (kappa_R = (1,k,k), other wall class-blind), k = alpha/2, weights fitted
# in protocol_readout_scan.py (PDG mixed scales).
alpha = 1 / 137.035999
k = alpha / 2
roots = [-1, -np.exp(2j * np.pi / 3), -np.exp(-2j * np.pi / 3)]
P = np.zeros((3, 3)); P[1, 0] = P[2, 1] = P[0, 2] = 1


def M(d, s, orient):
    X = d * np.eye(3, dtype=complex) + (P if orient == 1 else P.T)
    return np.diag([s, k, k]) @ X @ np.diag([s, 1, 1])


def sv(m):
    return np.sort(np.linalg.svd(m, compute_uv=False))


def left(m):
    return np.linalg.eigh(m @ m.conj().T)[1]


s_u, s_d = np.sqrt(1.3066), np.sqrt(0.0670)
print("Orientation test: same singular values in both orientations?",
      all(np.allclose(sv(M(d, s, 1)), sv(M(d, s, 2))) for d in roots for s in (s_u, s_d)))
print("CKM with up = orientation 1, down = orientation 2 (data 0.225, 0.041, 0.0037):")
for eu, ed, tag in [(0, 0, "on resonance"), (0.00236, 0.1396, "offsets fitted to m1/m2")]:
    for du, dd in [(0, 0), (0, 1)]:
        V = np.abs(left(M(roots[du] * (1 - eu), s_u, 1)).conj().T @
                   left(M(roots[dd] * (1 - ed), s_d, 2)))
        print(f"  {tag:24s} roots ({du},{dd}): |V_us| {V[0, 1]:.4f} |V_cb| {V[1, 2]:.4f} |V_ub| {V[0, 2]:.4f}")

# Charged-current moves on the reference wall F (class 0 = reference), with orientation as doublet.
print("Elementary moves (single-wall shifts and root moves) with generation and orientation:")
states = [(t, f) for t in range(3) for f in range(3) if t != f]
label = lambda s: 3 - s[0] - s[1]
orient = lambda s: 1 if s[1] == (s[0] + 1) % 3 else 2


def third(x, a):
    return None if a == x else 3 - x - a


for s in states:
    for a in range(3):
        nf = third(s[1], a)
        if nf is None or nf == s[0]:
            continue
        n = (s[0], nf)
        node = s[1] == 0 or n[1] == 0
        if orient(s) == 1:
            held = "up" if s[1] == 0 else ("down" if n[1] == 0 else "-")
            print(f"  F shift: up gen {label(s)} -> down gen {label(n)}  {'node' if node else 'direct'}"
                  f"  reference class held by: {held}")
