"""Colour and weak symmetry of the channel placement (check; no data).

EPLabelGen.channelE8Gen places the 16 channels as norm-4 vectors of the internal D4
(ChannelVectors.channelCoord: vector class for inactive channels, its triality image for
active ones). A gauge symmetry of the channels is realized by the placement only if it
preserves all inner products. This script tests that for the six colour permutations
(acting on both colour-triplet blocks) and for the weak flip (on both doublets).

Result (2026-11-23), every generation: of the six colour permutations only the identity and
the swap of colours 0 and 1 preserve the Gram matrix; colour 2 is special. The weak flip does
not preserve it either (the two members of each doublet are antipodal, v and -v, so pairings
with the singlets change sign). No isometry of the lattice can repair this, since any isometry
preserves the Gram matrix: the defect is in the channel-to-vector assignment (labelIndex,
active), which is a named placement premise. Consequence: the charge-correct mass-pair
transition (right singlet minus left doublet member, same colour) has norm 4, 4, 12 over the
three colours, so a pair count built on this placement would depend on colour.
Channel order: 0-5 quark doublet (2*colour + weak), 6-11 colour singlets (2*colour + {up, down}),
12-13 lepton doublet, 14 neutral singlet, 15 charged singlet.
"""
import json, numpy as np, itertools
import json, numpy as np
G=np.array([[2,0,-1,0,0,0,0,0],[0,2,0,-1,0,0,0,0],[-1,0,2,-1,0,0,0,0],[0,-1,-1,2,-1,0,0,0],
[0,0,0,-1,2,-1,0,0],[0,0,0,0,-1,2,-1,0],[0,0,0,0,0,-1,2,-1],[0,0,0,0,0,0,-1,2]])
cu=np.array([1,0,0,0,0,0,0,0]); cv=np.array([0,-2,-1,1,-1,0,0,0])
ip=lambda x,y:int(np.asarray(x)@G@np.asarray(y))
rd=lambda z:(lambda x:x if x<=21 else x-43)((ip(z,cu)-2*ip(z,cv))%43)
C=[{"g": 0, "pos": 0, "cls": 0, "v": [0, -1, -1, 0, 0, 0, 0, 0], "read": 28, "ic": [0, 2, 0, -2]}, {"g": 0, "pos": 1, "cls": 0, "v": [0, 1, 1, 0, 0, 0, 0, 0], "read": 15, "ic": [0, -2, 0, 2]}, {"g": 0, "pos": 2, "cls": 0, "v": [0, -1, -1, -2, 0, 0, 0, 0], "read": 9, "ic": [2, -2, 2, 0]}, {"g": 0, "pos": 3, "cls": 0, "v": [0, 1, 1, 2, 0, 0, 0, 0], "read": 34, "ic": [-2, 2, -2, 0]}, {"g": 0, "pos": 4, "cls": 0, "v": [0, 1, 1, 2, 2, 0, 0, 0], "read": 3, "ic": [-2, 0, 2, 0]}, {"g": 0, "pos": 5, "cls": 0, "v": [0, -1, -1, -2, -2, 0, 0, 0], "read": 40, "ic": [2, 0, -2, 0]}, {"g": 0, "pos": 6, "cls": 1, "v": [0, 0, 1, 2, 1, 0, 0, 0], "read": 30, "ic": [-2, 2, 0, 0]}, {"g": 0, "pos": 7, "cls": 2, "v": [0, 0, -1, -2, -1, 0, 0, 0], "read": 13, "ic": [2, -2, 0, 0]}, {"g": 0, "pos": 8, "cls": 1, "v": [0, 0, 1, 0, 1, 0, 0, 0], "read": 11, "ic": [0, -2, 2, 2]}, {"g": 0, "pos": 9, "cls": 2, "v": [0, 0, -1, 0, -1, 0, 0, 0], "read": 32, "ic": [0, 2, -2, -2]}, {"g": 0, "pos": 10, "cls": 1, "v": [0, 0, 1, 0, -1, 0, 0, 0], "read": 42, "ic": [0, 0, -2, 2]}, {"g": 0, "pos": 11, "cls": 2, "v": [0, 0, -1, 0, 1, 0, 0, 0], "read": 1, "ic": [0, 0, 2, -2]}, {"g": 0, "pos": 12, "cls": 3, "v": [0, -1, 1, 0, 0, 0, 0, 0], "read": 38, "ic": [0, 0, 0, 2]}, {"g": 0, "pos": 13, "cls": 3, "v": [0, 1, -1, 0, 0, 0, 0, 0], "read": 5, "ic": [0, 0, 0, -2]}, {"g": 0, "pos": 14, "cls": 4, "v": [0, -2, -1, -2, -1, 0, 0, 0], "read": 36, "ic": [2, 0, 0, 0]}, {"g": 0, "pos": 15, "cls": 5, "v": [0, 2, 1, 2, 1, 0, 0, 0], "read": 7, "ic": [-2, 0, 0, 0]}, {"g": 1, "pos": 0, "cls": 0, "v": [0, -1, 0, 0, -1, 0, 0, 0], "read": 27, "ic": [0, 2, -2, 0]}, {"g": 1, "pos": 1, "cls": 0, "v": [0, 1, 0, 0, 1, 0, 0, 0], "read": 16, "ic": [0, -2, 2, 0]}, {"g": 1, "pos": 2, "cls": 0, "v": [0, -1, 0, -2, -1, 0, 0, 0], "read": 8, "ic": [2, -2, 0, 2]}, {"g": 1, "pos": 3, "cls": 0, "v": [0, 1, 0, 2, 1, 0, 0, 0], "read": 35, "ic": [-2, 2, 0, -2]}, {"g": 1, "pos": 4, "cls": 0, "v": [0, -1, -2, -2, -1, 0, 0, 0], "read": 41, "ic": [2, 0, 0, -2]}, {"g": 1, "pos": 5, "cls": 0, "v": [0, 1, 2, 2, 1, 0, 0, 0], "read": 2, "ic": [-2, 0, 0, 2]}, {"g": 1, "pos": 6, "cls": 1, "v": [0, -1, -1, 0, 0, 0, 0, 0], "read": 28, "ic": [0, 2, 0, -2]}, {"g": 1, "pos": 7, "cls": 2, "v": [0, 1, 1, 0, 0, 0, 0, 0], "read": 15, "ic": [0, -2, 0, 2]}, {"g": 1, "pos": 8, "cls": 1, "v": [0, -1, -1, -2, 0, 0, 0, 0], "read": 9, "ic": [2, -2, 2, 0]}, {"g": 1, "pos": 9, "cls": 2, "v": [0, 1, 1, 2, 0, 0, 0, 0], "read": 34, "ic": [-2, 2, -2, 0]}, {"g": 1, "pos": 10, "cls": 1, "v": [0, 1, 1, 2, 2, 0, 0, 0], "read": 3, "ic": [-2, 0, 2, 0]}, {"g": 1, "pos": 11, "cls": 2, "v": [0, -1, -1, -2, -2, 0, 0, 0], "read": 40, "ic": [2, 0, -2, 0]}, {"g": 1, "pos": 12, "cls": 3, "v": [0, -1, 0, 0, 1, 0, 0, 0], "read": 39, "ic": [0, 0, 2, 0]}, {"g": 1, "pos": 13, "cls": 3, "v": [0, 1, 0, 0, -1, 0, 0, 0], "read": 4, "ic": [0, 0, -2, 0]}, {"g": 1, "pos": 14, "cls": 4, "v": [0, -1, 1, 0, 0, 0, 0, 0], "read": 38, "ic": [0, 0, 0, 2]}, {"g": 1, "pos": 15, "cls": 5, "v": [0, 1, -1, 0, 0, 0, 0, 0], "read": 5, "ic": [0, 0, 0, -2]}, {"g": 2, "pos": 0, "cls": 0, "v": [0, 0, 1, 2, 1, 0, 0, 0], "read": 30, "ic": [-2, 2, 0, 0]}, {"g": 2, "pos": 1, "cls": 0, "v": [0, 0, -1, -2, -1, 0, 0, 0], "read": 13, "ic": [2, -2, 0, 0]}, {"g": 2, "pos": 2, "cls": 0, "v": [0, 0, 1, 0, 1, 0, 0, 0], "read": 11, "ic": [0, -2, 2, 2]}, {"g": 2, "pos": 3, "cls": 0, "v": [0, 0, -1, 0, -1, 0, 0, 0], "read": 32, "ic": [0, 2, -2, -2]}, {"g": 2, "pos": 4, "cls": 0, "v": [0, 0, 1, 0, -1, 0, 0, 0], "read": 42, "ic": [0, 0, -2, 2]}, {"g": 2, "pos": 5, "cls": 0, "v": [0, 0, -1, 0, 1, 0, 0, 0], "read": 1, "ic": [0, 0, 2, -2]}, {"g": 2, "pos": 6, "cls": 1, "v": [0, -1, 0, 0, -1, 0, 0, 0], "read": 27, "ic": [0, 2, -2, 0]}, {"g": 2, "pos": 7, "cls": 2, "v": [0, 1, 0, 0, 1, 0, 0, 0], "read": 16, "ic": [0, -2, 2, 0]}, {"g": 2, "pos": 8, "cls": 1, "v": [0, -1, 0, -2, -1, 0, 0, 0], "read": 8, "ic": [2, -2, 0, 2]}, {"g": 2, "pos": 9, "cls": 2, "v": [0, 1, 0, 2, 1, 0, 0, 0], "read": 35, "ic": [-2, 2, 0, -2]}, {"g": 2, "pos": 10, "cls": 1, "v": [0, -1, -2, -2, -1, 0, 0, 0], "read": 41, "ic": [2, 0, 0, -2]}, {"g": 2, "pos": 11, "cls": 2, "v": [0, 1, 2, 2, 1, 0, 0, 0], "read": 2, "ic": [-2, 0, 0, 2]}, {"g": 2, "pos": 12, "cls": 3, "v": [0, -2, -1, -2, -1, 0, 0, 0], "read": 36, "ic": [2, 0, 0, 0]}, {"g": 2, "pos": 13, "cls": 3, "v": [0, 2, 1, 2, 1, 0, 0, 0], "read": 7, "ic": [-2, 0, 0, 0]}, {"g": 2, "pos": 14, "cls": 4, "v": [0, -1, 0, 0, 1, 0, 0, 0], "read": 39, "ic": [0, 0, 2, 0]}, {"g": 2, "pos": 15, "cls": 5, "v": [0, 1, 0, 0, -1, 0, 0, 0], "read": 4, "ic": [0, 0, -2, 0]}]
V=lambda g,p:np.array(C[16*g+p]['v'])
Q=lambda a,b:2*a+b; S=lambda a,b:6+2*a+b

def perm_pos(p, sigma):
    if p<6: a,b=divmod(p,2); return 2*sigma[a]+b
    if p<12: a,b=divmod(p-6,2); return 6+2*sigma[a]+b
    return p
def wperm(p):  # flip weak index in doublets
    if p<6: a,b=divmod(p,2); return 2*a+(1-b)
    if p in (12,13): return 25-p
    return p
for g in range(3):
    Gm=np.array([[ip(V(g,i),V(g,j)) for j in range(16)] for i in range(16)])
    res=[]
    for sigma in itertools.permutations(range(3)):
        P=[perm_pos(p,sigma) for p in range(16)]
        res.append(bool((Gm[np.ix_(P,P)]==Gm).all()))
    P=[wperm(p) for p in range(16)]
    print('g',g,'colour perms preserving Gram:',res,' weak flip preserves:',bool((Gm[np.ix_(P,P)]==Gm).all()))
g=0
Gm=np.array([[ip(V(g,i),V(g,j)) for j in range(16)] for i in range(16)])
print(Gm)
