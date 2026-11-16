#!/usr/bin/env python3
"""Protocol readout scan on the wire's light mass (PMAction.WireMass).

M = diag(s, k, k) . (delta + cyc(1, k, k)) . diag(s, 1, 1), K = 1, k = alpha/2.
s = 1 is the bare wire; s scales the heavy label on both walls.

Prints:
1. the cycle resonance delta_c = -(k^2)^(1/3), where det M = 0 (WireResonance);
2. m2/m3 on the resonance at s = 1 (the same for every protocol);
3. for each charged protocol, the heavy-label weight w = s^2 that reproduces its m2/m3 on the
   resonance, for a few common quark-mass ratio choices (quark ratios are scale dependent),
   and the correction gains k = w_e/w they imply if the weight is the minimum margin W/k
   (PMSubstrate.MinimumMargin) in lepton units.
"""
import numpy as np
from scipy.optimize import brentq

k = 1 / (2 * 137.035999)
dc = -k ** (2 / 3)


def M(d, s):
    X = d * np.eye(3)
    X[1, 0] += 1; X[2, 1] += k; X[0, 2] += k
    return np.diag([s, k, k]) @ X @ np.diag([s, 1, 1])


def ratios(d, s):
    sv = np.sort(np.linalg.svd(M(d, s), compute_uv=False))
    return sv[0] / sv[1], sv[1] / sv[2]


def weight(target):
    ss = np.logspace(-2, 2, 4000)
    v = [ratios(dc, s)[1] - target for s in ss]
    roots = [brentq(lambda s: ratios(dc, s)[1] - target, ss[i], ss[i + 1])
             for i in range(len(ss) - 1) if v[i] * v[i + 1] < 0]
    return roots[0] ** 2


print(f"delta_c = {dc:.6f}, det at delta_c = {np.linalg.det(M(dc, 1)):.2e}")
print(f"on resonance, s = 1: m2/m3 = {ratios(dc, 1)[1]:.5f}  (k^(2/3) = {k ** (2 / 3):.5f})")
for label, (lep, down, up) in {
        "PDG mixed scales": (0.0595, 0.0199, 0.00372),
        "M_Z running": (0.0595, 0.0187, 0.0036),
        "m_b, m_t own scale": (0.0595, 0.0223, 0.0042)}.items():
    we, wd, wu = weight(lep), weight(down), weight(up)
    print(f"{label:20s} w_e={we:.3f} w_d={wd:.3f} w_u={wu:.3f}  "
          f"w_d/w_e={wd / we:.2f} w_u/w_e={wu / we:.1f}  "
          f"gains k = w_e/w (lepton units): k_d={we / wd:.3f} k_u={we / wu:.4f} (1/{wu / we:.1f})")
