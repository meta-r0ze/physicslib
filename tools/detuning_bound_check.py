#!/usr/bin/env python3
"""Can a protocol-dependent detuning replace the heavy-label weight? (external, numerical)

Bare derived wire (s = 1, k = alpha/2; tools/protocol_readout_scan.py), any complex detuning delta.
Result: m2/m3 never exceeds its resonance value sqrt(3/2) k = 0.00447; the maximum is at the
cube roots delta^3 = -1. So no detuning reaches the larger ratios of the other protocols, and a
protocol-dependent ratio of heavy to node coupling (s/k) is needed
(EP REVIEW, heavy-label weight; EventRequirements.node_toll_raises_heavy).
Also printed: the charged selector's eigenphases (ChargedInsertion, step 3pi/4) used as detuning
phases, and, as a comparison only, the s/k factors the recorded ratios would need.
"""
import numpy as np
from scipy.optimize import brentq, minimize

a = 1 / 137.035999
k = a / 2


def M(d, s=1.0):
    X = d * np.eye(3, dtype=complex); X[1, 0] += 1; X[2, 1] += 1; X[0, 2] += 1
    return np.diag([s, k, k]) @ X @ np.diag([s, 1, 1])


def ratios(d, s=1.0):
    sv = np.sort(np.linalg.svd(M(d, s), compute_uv=False))
    return sv[0] / sv[1], sv[1] / sv[2]


best = 0.0
for rho in np.linspace(0, 3, 301):
    for th in np.linspace(-np.pi, np.pi, 361):
        best = max(best, ratios(rho * np.exp(1j * th))[1])
for x0 in ([-1, 0], [0.5, 0.866], [0.5, -0.866]):
    res = minimize(lambda v: -ratios(v[0] + 1j * v[1])[1], x0, method="Nelder-Mead",
                   options={"xatol": 1e-12, "fatol": 1e-16})
    best = max(best, -res.fun)
print(f"max over complex delta of m2/m3 = {best:.6f}; sqrt(3/2) k = {np.sqrt(1.5) * k:.6f}")
for lab, ph in [("vacancy", 1), ("e", 1j), ("u", -1), ("d", -1j)]:
    m12, m23 = ratios(-ph)
    print(f"selector phase {lab:8s}: delta = {-ph}: m1/m2 = {m12:.5f}, m2/m3 = {m23:.5f}")
print("comparison only: heavy/node factor s needed at resonance for recorded m2/m3")
for lab, t in [("e (m_mu/m_tau)", 0.0595), ("d (m_s/m_b)", 0.0199), ("u (m_c/m_t, M_Z)", 0.0036),
               ("u (m_c(m_c)/m_t)", 0.00734)]:
    s = brentq(lambda s: ratios(-1, s)[1] - t, 0.05, 50) if t > 0 else float("nan")
    print(f"  {lab:20s} s = {s:.3f}")
