#!/usr/bin/env python3
"""Protocol readout scan on the derived wire's light mass.

Wire (PMAction): M = diag(s, k, k) . (delta + cyc(1, 1, 1)) . diag(s, 1, 1).
- Reference wall kappa_R = (K, k, k), K = 1: only the label-v generation has a direct insertion;
  the other two need a reference-restoring process of amplitude k (PMAction.ReferenceClassHop).
- Other wall kappa_O = (1, 1, 1): class-blind (PMAction.CarrierAdmittance.uniform_hop).
- s = 1 is the bare wire; s scales the heavy label on both walls (the protocol weight w = s^2).
- k/K is open (PMAction REVIEW): two legs give alpha/2, one leg alpha.

Prints:
1. the cycle resonance delta^3 = -1 (PMAction.OtherWallStationary) and, for each cube root,
   the bare-wire m2/m3 (coherent law: singular values) and the lazy law ((m2/m3)^2,
   PMAction.WallOffset);
2. for each charged protocol, the heavy-label weight w = s^2 that reproduces its m2/m3 on the
   resonance (coherent law), for a few quark-mass ratio choices, and the weight ratios.
"""
import numpy as np
from scipy.optimize import brentq

alpha = 1 / 137.035999
roots = [-1, -np.exp(2j * np.pi / 3), -np.exp(-2j * np.pi / 3)]


def M(d, s, k):
    X = d * np.eye(3, dtype=complex)
    X[1, 0] += 1; X[2, 1] += 1; X[0, 2] += 1
    return np.diag([s, k, k]) @ X @ np.diag([s, 1, 1])


def m23(d, s, k):
    sv = np.sort(np.linalg.svd(M(d, s, k), compute_uv=False))
    return sv[1] / sv[2]


def weight(target, k, d=-1):
    ss = np.logspace(-3, 3, 6000)
    v = [m23(d, s, k) - target for s in ss]
    roots_ = [brentq(lambda s: m23(d, s, k) - target, ss[i], ss[i + 1])
              for i in range(len(ss) - 1) if v[i] * v[i + 1] < 0]
    return roots_[0] ** 2 if roots_ else float("nan")


for k, name in [(alpha / 2, "alpha/2"), (alpha, "alpha")]:
    print(f"k/K = {name} = {k:.5f}")
    for d in roots:
        r = m23(d, 1, k)
        sv = np.sort(np.linalg.svd(M(d, 1, k), compute_uv=False))
        print(f"  root {np.round(d, 3)}: m1/m3 = {sv[0] / sv[2]:.1e}, m2/m3 coherent = {r:.5f} "
              f"(sqrt(3/2) k = {np.sqrt(1.5) * k:.5f}), lazy = {r * r:.2e}")
    for label, (lep, down, up) in {
            "PDG mixed scales": (0.0595, 0.0199, 0.00372),
            "M_Z running": (0.0595, 0.0187, 0.0036),
            "m_b, m_t own scale": (0.0595, 0.0223, 0.0042)}.items():
        we, wd, wu = weight(lep, k), weight(down, k), weight(up, k)
        print(f"  {label:20s} w_e={we:.4f} w_d={wd:.4f} w_u={wu:.4f}  s_d/s_e={np.sqrt(wd / we):.2f} s_u/s_e={np.sqrt(wu / we):.1f}  "
              f"w_d/w_e={wd / we:.2f} w_u/w_e={wu / we:.1f}")

# CKM on the derived wire: V = U_u^H U_d, U the left eigenvectors (ascending masses) of M M^H,
# with each protocol's weight fitted above (k = alpha/2, PDG mixed scales).
k = alpha / 2
s_d, s_u = np.sqrt(weight(0.0199, k)), np.sqrt(weight(0.00372, k))


def left(d, s):
    m = M(d, s, k)
    return np.linalg.eigh(m @ m.conj().T)[1]


print("CKM (k = alpha/2; data |V_us| 0.225, |V_cb| 0.041, |V_ub| 0.0037):")
for same, (iu, id_) in [("same root", (0, 0)), ("different roots", (0, 1))]:
    V = np.abs(left(roots[iu], s_u).conj().T @ left(roots[id_], s_d))
    print(f"  {same:16s} |V_us| = {V[0, 1]:.4f}  |V_cb| = {V[1, 2]:.4f}  |V_ub| = {V[0, 2]:.4f}")
