#!/usr/bin/env python3
"""Comparison only: the down protocol as the geometric mean (HeavyFlipRecords.down_geometric_mean).

The exact two-bit record gives Tolls (2, 1, 0) for e, d, u, so for any price lam per registration
s = exp(-lam T/2) and s_d^2 = s_e s_u with no free parameter, and up keeps the bare wire (s_u = 1).
This script infers s from recorded mass ratios on the derived wire (k = alpha/2, delta = -1;
tools/protocol_readout_scan.py) for several quark-mass conventions and prints
  * s_d / sqrt(s_e s_u)          (1 if the law holds)
  * lam from e: ln(s_u/s_e), lam from d: 2 ln(s_u/s_d)   (equal if the law holds)
  * s_u                           (1 if up is the bare wire)
Data enter only here; nothing printed selects a derivation input.
"""
import numpy as np
from scipy.optimize import brentq

alpha = 1 / 137.035999
k = alpha / 2


def m23(s):
    X = -np.eye(3, dtype=complex); X[1, 0] += 1; X[2, 1] += 1; X[0, 2] += 1
    sv = np.sort(np.linalg.svd(np.diag([s, k, k]) @ X @ np.diag([s, 1, 1]), compute_uv=False))
    return sv[1] / sv[2]


def weight(t):
    return brentq(lambda s: m23(s) - t, 1e-3, 50)


lep = 206.768 / 3477
conventions = {
    "tier ledger (m_s(2GeV)/m_b(m_b), m_c(m_c)/m_t)": (93.54 / 4181.6, 1267.25 / 172671),
    "PDG mixed (scan)": (0.0199, 0.00372),
    "M_Z running (scan)": (0.0187, 0.0036),
    "scan 'own scale'": (0.0223, 0.0042),
}
print(f"{'convention':48s} {'s_e':>6s} {'s_d':>6s} {'s_u':>6s} {'s_d/sqrt':>9s} {'lam_e':>6s} {'lam_d':>6s}")
for lab, (d, u) in conventions.items():
    se, sd, su = weight(lep), weight(d), weight(u)
    print(f"{lab:48s} {se:6.3f} {sd:6.3f} {su:6.3f} {sd / np.sqrt(se * su):9.3f} "
          f"{np.log(su / se):6.3f} {2 * np.log(su / sd):6.3f}")
