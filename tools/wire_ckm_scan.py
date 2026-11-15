"""External scan (not a proof): two species-level tests of the wire's mass form
M = diag(K, k_s, k_c)(d + C) of PMFlavor.ReferenceWallMass, with the node rule's equal light
carriers |k_s| = |k_c| = k (tools/node_carrier_scan.py) and K = 1. For each sector the two mass
ratios at M_Z fix (k, d) up to a few discrete branches (node_carrier_scan.required_k); nothing else
is fitted.

Test 1 (common detuning). Premise under test: the other wall's detuning delta_O is a wire property,
one number for every species, and protocols change only the carrier scale lambda (all carriers
times lambda). Scaling gives M(lambda) = lambda^2 diag(..)(delta_O/lambda + C), so the fitted d is
delta_O/lambda and the heavy mass is E0 lambda^2 h(k, d), h the heavy singular value at K = 1.
Then d sqrt(m_heavy/h) = delta_O/sqrt(E0) must be one number for all sectors.
Result: leptons 0.084, 0.090, 0.308, 0.332; down 0.261, 0.351; up 0.502, 0.936 (one value per
branch). Up is at least 1.4x from every down branch. So a species-blind delta_O with protocol-set
carrier scales fails on up quarks (a 43% miss at the closest branch pair); leptons and down admit
one value within 6-30% on some branch pair, which is weak evidence given the branch count.

Test 2 (CKM from masses alone). The working CKM reading is U_u^H U_d (PMFlavor). With both sectors
on the equal-carrier form and fitted to their own mass ratios, there is no free parameter left.
Result over all 8 distinct branch and sign combinations: |V_cb| is 0.071 to 0.195 (data 0.0418),
|V_us| 0.083 to 0.376 (data 0.225), |V_ub| 0.0010 to 0.017 (data 0.0037). No combination fits; the
closest |V_us| (0.216, 0.247) come with |V_cb| = 0.071-0.076, 1.7x high. So with equal light
carriers in both sectors the up rotation cannot cancel enough of the down rotation's 0.14. Negative
result: the up protocol must give unequal light carriers (|k_s| != |k_c|) or change the form, and
the ratio k_s/k_c must then be derived, not fitted (fitting it uses up the |V_cb| test).

Mass inputs at M_Z (Xing, Zhang, Zhou 2008 style): m_t = 172.9, m_b = 2.86, m_tau = 1.7468 GeV; the
ratios are node_carrier_scan.DATA. CKM magnitudes: PDG 2024 global fit.

Usage: python3 tools/wire_ckm_scan.py   (needs numpy, scipy; imports tools/node_carrier_scan.py)
"""
import itertools, os, sys
import numpy as np
from scipy.optimize import least_squares
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import node_carrier_scan as n

MHEAVY = {"leptons": 1.7468, "down": 2.86, "up": 172.9}
CKM = np.array([[0.97435, 0.22500, 0.00369], [0.22486, 0.97349, 0.04182], [0.00857, 0.04110, 0.99912]])

def fits(sec, rng, starts=300):
    out = []
    for sign in (1, -1):
        for _ in range(starts):
            f = lambda p: np.log(n.ratios(10 ** p[0], sign, p[1])) - np.log(n.DATA[sec])
            r = least_squares(f, [rng.uniform(-6, 0), rng.uniform(-1, 1)])
            if r.cost < 1e-12:
                k, d = 10 ** r.x[0], r.x[1]
                if not any(abs(k - a) < 1e-6 * max(1, k) and abs(d - b) < 1e-6 and s == sign
                           for a, b, s in out):
                    out.append((k, d, sign))
    return out

def heavy(k, d, sign):
    return np.linalg.svd(n.mass(1.0, k, sign * k, d), compute_uv=False).max()

def left(k, d, sign):
    U, s, _ = np.linalg.svd(n.mass(1.0, k, sign * k, d)); return U[:, np.argsort(s)]

if __name__ == "__main__":
    rng = np.random.default_rng(1)
    S = {sec: fits(sec, rng) for sec in n.DATA}
    print("Test 1: delta_O / sqrt(E0) = |d| sqrt(m_heavy / h)")
    for sec, L in S.items():
        vals = sorted({round(abs(d) * np.sqrt(MHEAVY[sec] / heavy(k, d, s)), 3) for k, d, s in L})
        print(f"  {sec:8s} {vals}")
    print("Test 2: |V| = |U_u^H U_d| with no free parameter")
    seen = set()
    for u, dn in itertools.product(S["up"], S["down"]):
        V = np.abs(left(*u).conj().T @ left(*dn))
        key = (round(V[0, 1], 4), round(V[1, 2], 4))
        if key in seen: continue
        seen.add(key)
        print(f"  Vus={V[0,1]:.4f} Vcb={V[1,2]:.4f} Vub={V[0,2]:.5f} Vtd={V[2,0]:.5f}")
    print(f"  data Vus={CKM[0,1]} Vcb={CKM[1,2]} Vub={CKM[0,2]} Vtd={CKM[2,0]}")
