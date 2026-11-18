#!/usr/bin/env python3
"""Gap over light band on the bare derived wire (external, numerical; substrate inputs only).

Two-wall wire of tools/first_row_readout.py with the derived inputs only: heavy weight s = 1 (bare
wire), node coupling k = alpha/2 (PMAction.ReferenceNode), exact resonance delta = -1
(PMAction.OtherWallStationary). For each clock ratio r = K_f/|y| print the lowest gapped |E| over
the light band's top. A light parent releases less energy than its mass, which is at most that
top, so gapped daughters are never kinematically open (EP OVERVIEW, daughter channels).
No recorded mass enters.
"""
import numpy as np
a = 1 / 137.035999
k = a / 2


def H(r, s=1.0, d=-1.0):
    D1 = r * np.diag([s, k, k]).astype(complex)
    X = d * np.eye(3, dtype=complex); X[1, 0] += 1; X[2, 1] += 1; X[0, 2] += 1
    D2 = r * X @ np.diag([s, 1, 1]); Z = np.zeros((3, 3)); Y = np.eye(3)
    return np.block([[Z, D1, Z, Z], [D1.conj().T, Z, -Y, Z], [Z, -Y, Z, D2], [Z, Z, D2.conj().T, Z]])


for r in (1 / 8, 1 / 6, 1 / 4, 1 / 3, 1 / 2):
    E = np.sort(abs(np.linalg.eigvalsh(H(r))))
    print(f"r = {r:.3f}: light top {E[5]:.3e}, gap bottom {E[6]:.3f}, ratio {E[6] / E[5]:.1f}")
