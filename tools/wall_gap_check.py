#!/usr/bin/env python3
"""Are the wire's gapped modes open daughter channels? (external, numerical)

Two-wall wire of tools/first_row_readout.py (fitted weights s and offsets eps from EP OVERVIEW).
For each protocol and clock ratio r = K_f/|y|, the ratio of the lowest gapped |E| to the heaviest
light |E|, times that protocol's heaviest recorded mass, bounds the gapped modes' mass.
All exceed 75 GeV, far above the first-row (MeV) and muon (m_mu) energies: the gapped modes are
closed channels, so current weight on them is lost.
"""
import numpy as np
a=1/137.035999; k=a/2
def H(r,s,d=-1.0):
    D1=r*np.diag([s,k,k]).astype(complex)
    X=d*np.eye(3,dtype=complex); X[1,0]+=1; X[2,1]+=1; X[0,2]+=1
    D2=r*X@np.diag([s,1,1]); Z=np.zeros((3,3)); Y=np.eye(3)
    return np.block([[Z,D1,Z,Z],[D1.conj().T,Z,-Y,Z],[Z,-Y,Z,D2],[Z,Z,D2.conj().T,Z]])
heavy={"e (tau, 1.777 GeV)":(0.087,0.038,1.777),"d (b, 4.18 GeV)":(0.26,0.14,4.18),"u (t, 172.6 GeV)":(1.14,0.0024,172.6)}
for r in (1/8,1/4,1/2):
    for lab,(s,eps,mh) in heavy.items():
        E=np.sort(abs(np.linalg.eigvalsh(H(r,s,-1+eps))))
        light=E[:6]; gapped=E[6:]
        ratio=gapped.min()/light.max()
        print(f"r={r:.3f} {lab:20s} gapped/heaviest-light = {ratio:8.1f}  -> gapped mass >= {ratio*mh:9.1f} GeV")
